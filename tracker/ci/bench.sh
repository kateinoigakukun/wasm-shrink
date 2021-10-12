#!/bin/bash

tracker_dir="$(cd "$(dirname "$0")/.." && pwd)"
cd "$tracker_dir"
cargo run --bin wasm-shrink-tracker update $tracker_dir/.. --data html/data.json
