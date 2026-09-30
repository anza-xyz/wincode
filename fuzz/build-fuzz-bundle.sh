#!/bin/bash

set -e

# Get the commit hash
COMMIT=$(git rev-parse --short=10 HEAD)

# Get the repository URL
REPO_URL=$(git remote get-url origin 2>/dev/null || echo "https://github.com/anza-xyz/wincode")

# Get the list of fuzz targets
FUZZ_TARGETS=$(cargo fuzz list 2>/dev/null)

if [ -z "$FUZZ_TARGETS" ]; then
    echo "Error: No fuzz targets found or cargo fuzz list failed" >&2
    exit 1
fi

# Create the bundle directory
BUNDLE_DIR="./fuzz/target/bundle"
mkdir -p "$BUNDLE_DIR"

# Convert fuzz targets to array
targets=($FUZZ_TARGETS)
total=${#targets[@]}
count=0

# Copy binaries to bundle
echo "Copying binaries to $BUNDLE_DIR..."
for target in "${targets[@]}"; do
    binary_src="./fuzz/target/x86_64-unknown-linux-gnu/release/$target"
    if [ -f "$binary_src" ]; then
        cp "$binary_src" "$BUNDLE_DIR/"
        echo "  Copied: $target"
    else
        echo "  Warning: Binary not found: $binary_src" >&2
    fi
done

# Copy coverage binaries to bundle
RUSTFLAGS="-C instrument-coverage --cfg fuzzing" cargo +nightly fuzz build
for target in "${targets[@]}"; do
    binary_src="./fuzz/target/x86_64-unknown-linux-gnu/release/$target"
    if [ -f "$binary_src" ]; then
        cp "$binary_src" "$BUNDLE_DIR/${target}_cov"
        echo "  Copied: ${target}_cov"
    else
        echo "  Warning: Binary not found: $binary_src" >&2
    fi
done

# Generate manifest.fc.json
MANIFEST_FILE="$BUNDLE_DIR/manifest.fc.json"
echo "Generating $MANIFEST_FILE..."

cat <<EOF > "$MANIFEST_FILE"
{
	"version": 3,
	"revision": {
		"commit": "$COMMIT",
		"checkouts": {
			"$REPO_URL": "$COMMIT"
		}
	},

	"lineages": [
EOF

count=0
for target in "${targets[@]}"; do
    count=$((count + 1))
    
    # Binary path in bundle (just the filename since it's in the same directory)
    binary_path="./$target"
	coverage_binary_path="./${target}_cov"
    
    # Add comma for all but the last item
    if [ $count -lt $total ]; then
        comma=","
    else
        comma=""
    fi
    
    cat <<EOF >> "$MANIFEST_FILE"
		{
			"name": "$target",
			"confs": [
				{
					"name": "$target",
					"driver": {
						"type": "libfuzzer",
						"params": {
							"binary_path_in_bundle": "$binary_path",
							"coverage_binary_path_in_bundle": "$coverage_binary_path",
							"sources_path_in_bundle": "./src/",
							"sources_original_path": "$(pwd)"
						}
					},
					"architecture": {
						"name": "amd64"
					},
					"memory_kib": 1048576,
					"cores": 1
				}
			]
		}$comma
EOF
done

cat <<EOF >> "$MANIFEST_FILE"
	]
}
EOF

# Copy source for coverage reports
mkdir -p "$BUNDLE_DIR/src"
find . -type f -name '*.rs' ! -path '*/bundle/*' ! -path '*/target/*' |
  rsync -R --files-from=- . "$BUNDLE_DIR/src/"

echo "Done! Bundle created at $BUNDLE_DIR"
echo "Contents:"
ls -la "$BUNDLE_DIR"