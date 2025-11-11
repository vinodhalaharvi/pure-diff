// main.go
package main

import (
	"crypto/sha256"
	"embed"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"io/fs"
	"net"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"
	"sync"
	"time"
)

//go:embed index.html
var content embed.FS

// ============================================================================
// DEFERRED COMPUTATION - Simple thunks for lazy evaluation
// Note: This is not a true "Free Applicative" - just deferred execution
// ============================================================================

type Thunk[A any] struct {
	Compute func() A
	Name    string
}

func RunThunk[A any](t Thunk[A]) A {
	return t.Compute()
}

// ParallelRunThunks executes thunks in parallel with N workers
func ParallelRunThunks[A any](thunks []Thunk[A], numWorkers int) []A {
	if numWorkers <= 0 {
		numWorkers = 1
	}

	results := make([]A, len(thunks))
	jobs := make(chan int, len(thunks))
	var wg sync.WaitGroup

	for w := 0; w < numWorkers; w++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for idx := range jobs {
				results[idx] = RunThunk(thunks[idx])
			}
		}()
	}

	for i := range thunks {
		jobs <- i
	}
	close(jobs)

	wg.Wait()
	return results
}

// ============================================================================
// DOMAIN TYPES
// ============================================================================

type MerkleNode struct {
	Hash     []byte
	Children []MerkleNode
	IsLeaf   bool
}

type FileTree struct {
	Path       string
	Root       []byte
	Tree       MerkleNode
	Size       int64
	ChunkCount int
	Leaves     []string
	Depth      int
}

type DuplicateMatch struct {
	TargetPath string
	Similarity float64
	SharedSize int64
}

type FileNode struct {
	Path         string
	Name         string
	IsDir        bool
	Children     []FileNode
	Matches      []DuplicateMatch
	BestMatch    float64
	Size         int64
	RelativePath string
}

type DedupResult struct {
	SourceTree      FileNode
	AllMatches      map[string][]DuplicateMatch
	TotalFiles      int
	UniqueFiles     int
	FullDupCount    int
	PartialDupCount int
	SpaceSaved      int64
}

// ============================================================================
// MONOID
// ============================================================================

type Monoid[A any] struct {
	Empty   func() A
	Combine func(A, A) A
}

var SHA256Monoid = Monoid[[]byte]{
	Empty: func() []byte { return []byte{} },
	Combine: func(a, b []byte) []byte {
		h := sha256.New()
		h.Write(a)
		h.Write(b)
		return h.Sum(nil)
	},
}

// ============================================================================
// UTILITY FUNCTIONS
// ============================================================================

func Map[A, B any](xs []A, f func(A) B) []B {
	result := make([]B, len(xs))
	for i, x := range xs {
		result[i] = f(x)
	}
	return result
}

func Filter[A any](xs []A, pred func(A) bool) []A {
	result := []A{}
	for _, x := range xs {
		if pred(x) {
			result = append(result, x)
		}
	}
	return result
}

func GroupBy[A any, K comparable](xs []A, key func(A) K) map[K][]A {
	groups := make(map[K][]A)
	for _, x := range xs {
		k := key(x)
		groups[k] = append(groups[k], x)
	}
	return groups
}

// ============================================================================
// MERKLE TREE
// ============================================================================

func HashLeaf(data []byte) []byte {
	h := sha256.Sum256(data)
	return h[:]
}

func BuildMerkleTree(hashes [][]byte, m Monoid[[]byte]) MerkleNode {
	if len(hashes) == 0 {
		return MerkleNode{Hash: m.Empty(), IsLeaf: true, Children: []MerkleNode{}}
	}
	if len(hashes) == 1 {
		return MerkleNode{Hash: hashes[0], IsLeaf: true, Children: []MerkleNode{}}
	}

	nextLevel := []MerkleNode{}

	for i := 0; i < len(hashes); i += 2 {
		if i+1 < len(hashes) {
			left := MerkleNode{Hash: hashes[i], IsLeaf: true, Children: []MerkleNode{}}
			right := MerkleNode{Hash: hashes[i+1], IsLeaf: true, Children: []MerkleNode{}}
			combined := m.Combine(hashes[i], hashes[i+1])

			parent := MerkleNode{
				Hash:     combined,
				IsLeaf:   false,
				Children: []MerkleNode{left, right},
			}
			nextLevel = append(nextLevel, parent)
		} else {
			single := MerkleNode{Hash: hashes[i], IsLeaf: true, Children: []MerkleNode{}}
			nextLevel = append(nextLevel, single)
		}
	}

	if len(nextLevel) == 1 {
		return nextLevel[0]
	}

	parentHashes := Map(nextLevel, func(n MerkleNode) []byte { return n.Hash })
	upperTree := BuildMerkleTree(parentHashes, m)
	upperTree.Children = nextLevel
	return upperTree
}

func collectLeaves(node MerkleNode) [][]byte {
	if node.IsLeaf {
		return [][]byte{node.Hash}
	}

	leaves := [][]byte{}
	for _, child := range node.Children {
		childLeaves := collectLeaves(child)
		leaves = append(leaves, childLeaves...)
	}
	return leaves
}

// ============================================================================
// FILE PROCESSING
// ============================================================================

func calculateDepth(rootDir, filePath string) int {
	rel, err := filepath.Rel(rootDir, filePath)
	if err != nil {
		return 0
	}
	if rel == "." {
		return 0
	}
	return strings.Count(rel, string(filepath.Separator)) + 1
}

func ProcessFileThunk(path string, chunkSize int, rootDir string) Thunk[FileTree] {
	return Thunk[FileTree]{
		Compute: func() FileTree {
			file, err := os.Open(path)
			if err != nil {
				return FileTree{}
			}
			defer file.Close()

			stat, err := file.Stat()
			if err != nil {
				return FileTree{}
			}

			chunks := [][]byte{}
			buffer := make([]byte, chunkSize)

			for {
				n, err := file.Read(buffer)
				if n > 0 {
					chunk := make([]byte, n)
					copy(chunk, buffer[:n])
					chunks = append(chunks, chunk)
				}
				if err == io.EOF {
					break
				}
				if err != nil {
					return FileTree{}
				}
			}

			hashes := Map(chunks, HashLeaf)

			// Build tree once and extract root from it (no redundant hashing)
			tree := BuildMerkleTree(hashes, SHA256Monoid)
			root := tree.Hash

			// Pre-compute leaves as hex strings
			leafBytes := collectLeaves(tree)
			leaves := Map(leafBytes, func(b []byte) string {
				return hex.EncodeToString(b)
			})

			depth := calculateDepth(rootDir, path)

			return FileTree{
				Path:       path,
				Root:       root,
				Tree:       tree,
				Size:       stat.Size(),
				ChunkCount: len(chunks),
				Leaves:     leaves,
				Depth:      depth,
			}
		},
		Name: fmt.Sprintf("ProcessFile(%s)", filepath.Base(path)),
	}
}

// ScanDirectoryThunk scans directory and respects maxDepth
func ScanDirectoryThunk(dir string, maxDepth int) Thunk[[]string] {
	return Thunk[[]string]{
		Compute: func() []string {
			var files []string

			filepath.Walk(dir, func(path string, info os.FileInfo, err error) error {
				if err != nil {
					return nil
				}

				// Calculate depth
				depth := calculateDepth(dir, path)

				// Skip directories that are too deep
				if info.IsDir() && depth > maxDepth {
					return filepath.SkipDir
				}

				// Only add files (not directories) within depth limit
				if !info.IsDir() && depth <= maxDepth {
					files = append(files, path)
				}

				return nil
			})

			return files
		},
		Name: fmt.Sprintf("ScanDir(%s, maxDepth=%d)", filepath.Base(dir), maxDepth),
	}
}

// ============================================================================
// OPTIMIZED DEDUPLICATION
// ============================================================================

func BuildChunkIndex(files []FileTree) map[string][]int {
	index := make(map[string][]int)
	for i, file := range files {
		for _, chunkHash := range file.Leaves {
			index[chunkHash] = append(index[chunkHash], i)
		}
	}
	return index
}

func FindCandidates(sourceFile FileTree, chunkIndex map[string][]int, threshold float64) map[int]int {
	candidates := make(map[int]int)

	for _, chunkHash := range sourceFile.Leaves {
		if targets, exists := chunkIndex[chunkHash]; exists {
			for _, targetIdx := range targets {
				candidates[targetIdx]++
			}
		}
	}

	minSharedChunks := int(float64(len(sourceFile.Leaves)) * threshold)
	filtered := make(map[int]int)
	for idx, count := range candidates {
		if count >= minSharedChunks {
			filtered[idx] = count
		}
	}

	return filtered
}

func CompareFiles(a, b FileTree) float64 {
	if hex.EncodeToString(a.Root) == hex.EncodeToString(b.Root) {
		return 1.0
	}

	if len(a.Leaves) == 0 || len(b.Leaves) == 0 {
		return 0.0
	}

	setB := make(map[string]bool, len(b.Leaves))
	for _, leaf := range b.Leaves {
		setB[leaf] = true
	}

	matches := 0
	for _, leaf := range a.Leaves {
		if setB[leaf] {
			matches++
		}
	}

	return float64(matches) / float64(len(a.Leaves))
}

// ============================================================================
// TREE BUILDING
// ============================================================================

func BuildFileTree(rootPath string, files []FileTree, matches map[string][]DuplicateMatch, maxDepth int) FileNode {
	relFiles := make(map[string]FileTree)
	for _, f := range files {
		rel, _ := filepath.Rel(rootPath, f.Path)
		relFiles[rel] = f
	}

	root := FileNode{
		Path:         rootPath,
		Name:         filepath.Base(rootPath),
		IsDir:        true,
		Children:     []FileNode{},
		RelativePath: "",
	}

	for rel, ft := range relFiles {
		parts := strings.Split(rel, string(filepath.Separator))
		addToTree(&root, parts, ft, matches, 1, maxDepth, rootPath)
	}

	return root
}

func addToTree(node *FileNode, parts []string, ft FileTree, matches map[string][]DuplicateMatch, depth int, maxDepth int, rootPath string) {
	if depth > maxDepth {
		return
	}

	if len(parts) == 0 {
		return
	}

	if len(parts) == 1 {
		fileMatches := matches[ft.Path]
		bestMatch := 0.0
		if len(fileMatches) > 0 {
			for _, m := range fileMatches {
				if m.Similarity > bestMatch {
					bestMatch = m.Similarity
				}
			}
		}

		node.Children = append(node.Children, FileNode{
			Path:         ft.Path,
			Name:         parts[0],
			IsDir:        false,
			Children:     []FileNode{},
			Matches:      fileMatches,
			BestMatch:    bestMatch,
			Size:         ft.Size,
			RelativePath: ft.Path,
		})
		return
	}

	dirName := parts[0]
	var dirNode *FileNode
	for i := range node.Children {
		if node.Children[i].Name == dirName && node.Children[i].IsDir {
			dirNode = &node.Children[i]
			break
		}
	}

	if dirNode == nil {
		// Build full path for this directory node
		currentPath := filepath.Join(node.Path, dirName)
		relativePath, _ := filepath.Rel(rootPath, currentPath)

		node.Children = append(node.Children, FileNode{
			Name:         dirName,
			Path:         currentPath,
			RelativePath: relativePath,
			IsDir:        true,
			Children:     []FileNode{},
		})
		dirNode = &node.Children[len(node.Children)-1]
	}

	addToTree(dirNode, parts[1:], ft, matches, depth+1, maxDepth, rootPath)
}

// ============================================================================
// MAIN DEDUPLICATION LOGIC
// ============================================================================

func FindDuplicatesThunk(sourceDir, targetDir string, threshold float64, maxDepth int, numWorkers int, chunkSize int) Thunk[DedupResult] {
	sourceScan := ScanDirectoryThunk(sourceDir, maxDepth)
	targetScan := ScanDirectoryThunk(targetDir, maxDepth)

	return Thunk[DedupResult]{
		Compute: func() DedupResult {
			// Step 1: Scan directories (with maxDepth filtering)
			sourceFiles := RunThunk(sourceScan)
			targetFiles := RunThunk(targetScan)

			// Step 2: Build thunks for all files
			sourceThunks := Map(sourceFiles, func(path string) Thunk[FileTree] {
				return ProcessFileThunk(path, chunkSize, sourceDir)
			})
			targetThunks := Map(targetFiles, func(path string) Thunk[FileTree] {
				return ProcessFileThunk(path, chunkSize, targetDir)
			})

			// Step 3: Execute in parallel
			sourceTrees := Filter(ParallelRunThunks(sourceThunks, numWorkers), func(ft FileTree) bool {
				return ft.Path != ""
			})
			targetTrees := Filter(ParallelRunThunks(targetThunks, numWorkers), func(ft FileTree) bool {
				return ft.Path != ""
			})

			// Step 4: Phase 1 - Group by merkle root (exact duplicates)
			targetByRoot := GroupBy(targetTrees, func(ft FileTree) string {
				return hex.EncodeToString(ft.Root)
			})

			allMatches := make(map[string][]DuplicateMatch)
			fullDupCount := 0
			partialDupCount := 0
			spaceSaved := int64(0)

			exactMatchSources := []FileTree{}
			remainingSources := []FileTree{}

			for _, src := range sourceTrees {
				rootKey := hex.EncodeToString(src.Root)
				if targets, exists := targetByRoot[rootKey]; exists && len(targets) > 0 {
					matches := Map(targets, func(tgt FileTree) DuplicateMatch {
						return DuplicateMatch{
							TargetPath: tgt.Path,
							Similarity: 1.0,
							SharedSize: src.Size,
						}
					})
					allMatches[src.Path] = matches
					fullDupCount++
					spaceSaved += src.Size
					exactMatchSources = append(exactMatchSources, src)
				} else {
					remainingSources = append(remainingSources, src)
				}
			}

			// Step 5: Phase 2 - Build inverted index
			remainingTargets := []FileTree{}
			for _, tgt := range targetTrees {
				rootKey := hex.EncodeToString(tgt.Root)
				isExactMatch := false
				for _, src := range exactMatchSources {
					if hex.EncodeToString(src.Root) == rootKey {
						isExactMatch = true
						break
					}
				}
				if !isExactMatch {
					remainingTargets = append(remainingTargets, tgt)
				}
			}

			chunkIndex := BuildChunkIndex(remainingTargets)

			// Step 6: Find partial duplicates
			for _, src := range remainingSources {
				candidates := FindCandidates(src, chunkIndex, threshold)

				matches := []DuplicateMatch{}
				for targetIdx := range candidates {
					tgt := remainingTargets[targetIdx]
					similarity := CompareFiles(src, tgt)

					if similarity >= threshold && similarity < 1.0 {
						matches = append(matches, DuplicateMatch{
							TargetPath: tgt.Path,
							Similarity: similarity,
							SharedSize: int64(float64(src.Size) * similarity),
						})
					}
				}

				if len(matches) > 0 {
					allMatches[src.Path] = matches
					partialDupCount++
				}
			}

			// Step 7: Build UI tree
			tree := BuildFileTree(sourceDir, sourceTrees, allMatches, maxDepth)

			uniqueCount := len(sourceTrees) - fullDupCount - partialDupCount

			return DedupResult{
				SourceTree:      tree,
				AllMatches:      allMatches,
				TotalFiles:      len(sourceTrees),
				UniqueFiles:     uniqueCount,
				FullDupCount:    fullDupCount,
				PartialDupCount: partialDupCount,
				SpaceSaved:      spaceSaved,
			}
		},
		Name: fmt.Sprintf("FindDuplicates(src:%s, tgt:%s, thresh:%.0f%%, depth:%d, workers:%d, chunk:%d)",
			filepath.Base(sourceDir), filepath.Base(targetDir), threshold*100, maxDepth, numWorkers, chunkSize),
	}
}

// ============================================================================
// HTTP SERVER
// ============================================================================

func handleDedup(w http.ResponseWriter, r *http.Request) {
	if r.Method != "POST" {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	var req struct {
		SourceDir  string  `json:"sourceDir"`
		TargetDir  string  `json:"targetDir"`
		Threshold  float64 `json:"threshold"`
		MaxDepth   int     `json:"maxDepth"`
		NumWorkers int     `json:"numWorkers"`
		ChunkSize  int     `json:"chunkSize"`
	}

	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}

	if req.NumWorkers <= 0 {
		req.NumWorkers = runtime.NumCPU()
	}

	if req.ChunkSize <= 0 {
		req.ChunkSize = 4096
	}

	dedupThunk := FindDuplicatesThunk(req.SourceDir, req.TargetDir, req.Threshold, req.MaxDepth, req.NumWorkers, req.ChunkSize)

	result := RunThunk(dedupThunk)
	json.NewEncoder(w).Encode(result)
}

func openBrowser(url string) {
	var err error
	switch runtime.GOOS {
	case "linux":
		err = exec.Command("xdg-open", url).Start()
	case "windows":
		err = exec.Command("rundll32", "url.dll,FileProtocolHandler", url).Start()
	case "darwin":
		err = exec.Command("open", url).Start()
	}
	if err != nil {
		fmt.Println("Please open your browser to:", url)
	}
}

// findAvailablePort tries to find an available port starting from startPort
func findAvailablePort(startPort int) (int, error) {
	for port := startPort; port < startPort+100; port++ {
		addr := fmt.Sprintf(":%d", port)
		listener, err := net.Listen("tcp", addr)
		if err == nil {
			listener.Close()
			return port, nil
		}
	}
	return 0, fmt.Errorf("no available ports found")
}

// waitForServer waits for the server to be ready
func waitForServer(url string, timeout time.Duration) bool {
	deadline := time.Now().Add(timeout)
	for time.Now().Before(deadline) {
		resp, err := http.Get(url)
		if err == nil {
			resp.Body.Close()
			return true
		}
		time.Sleep(50 * time.Millisecond)
	}
	return false
}

// ============================================================================
// MAIN
// ============================================================================

func main() {
	// Find available port
	port, err := findAvailablePort(8080)
	if err != nil {
		fmt.Println("Error finding available port:", err)
		return
	}

	fsys, err := fs.Sub(content, ".")
	if err != nil {
		panic(err)
	}
	http.Handle("/", http.FileServer(http.FS(fsys)))
	http.HandleFunc("/api/dedup", handleDedup)

	url := fmt.Sprintf("http://localhost:%d", port)

	fmt.Println("🚀 pure-diff - Content-based file comparison")
	fmt.Println("📊 Server:", url)
	fmt.Println("🔍 Parallel execution + Inverted index + Monoidal grouping")
	fmt.Println("🌳 Merkle tree content deduplication")
	fmt.Printf("💻 Default workers: %d (CPU cores)\n", runtime.NumCPU())
	fmt.Println()

	// Start server in background
	serverReady := make(chan bool)
	go func() {
		listener, err := net.Listen("tcp", fmt.Sprintf(":%d", port))
		if err != nil {
			fmt.Println("Error starting server:", err)
			serverReady <- false
			return
		}
		serverReady <- true
		http.Serve(listener, nil)
	}()

	// Wait for server to be ready
	if <-serverReady {
		if waitForServer(url, 5*time.Second) {
			openBrowser(url)
		} else {
			fmt.Println("Server started but not responding. Please open your browser to:", url)
		}
	}

	// Keep main goroutine alive
	select {}
}
