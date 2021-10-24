#!/bin/bash

repo_root="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$repo_root"
git checkout origin/gh-pages ./data
mv $repo_root/data/*.json $repo_root/tracker/html/data
