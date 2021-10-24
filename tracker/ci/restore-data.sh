#!/bin/bash

repo_root="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$repo_root"
git checkout origin/gh-pages ./data
mv $repo_root/data $repo_root/tracker/html/data
