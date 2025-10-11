function main() {
    const maxDepth = 10;
    const stretchDepth = maxDepth + 1;
    const stretchTree = createTree(stretchDepth)
    console.log(`stretch tree of depth ${stretchDepth}\t check: ${checksum(stretchTree)}`)
    const longLivedTree = createTree(maxDepth);

    for (let depth = 4; depth <= maxDepth; depth += 2) {
        const iterations = 1 << maxDepth - depth + 4;
        let sum = 0;
        for (var i = 0; i < iterations; i++) {
            const tree = createTree(depth)
            sum += checksum(tree)
        }
        console.log(`${iterations}\t trees of depth ${depth}\t check: ${sum}`)
    }

    console.log(
        `long lived tree of depth ${maxDepth}\t check: ${checksum(longLivedTree)}`
    );
}

function checksum(node) {
    if (!node.left) {
        return 1;
    }
    return 1 + checksum(node.left) + checksum(node.right);
}

function createTree(depth) {
    return depth-- > 0
        ? { left: createTree(depth), right: createTree(depth) }
        : { left: null, right: null };
}

var t0 = performance.now();     // 1) start
main()
var t1 = performance.now();     // 2) end
var dt = t1 - t0;               // 3) difference
var secs = dt / 1000;           // 4) milliseconds to seconds
console.log(`Execution time: ${secs.toFixed(6)} s`);  // 5) print