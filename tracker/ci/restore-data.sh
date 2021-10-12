#!/bin/bash

repo_root="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$repo_root"
git checkout gh-pages ./data.json
mv $repo_root/data.json $repo_root/tracker/html/data.json
