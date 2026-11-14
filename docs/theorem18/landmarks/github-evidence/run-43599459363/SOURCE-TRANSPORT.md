# Lossless source archive transport

The original `source.tar.gz` is 105,878,979 bytes, exceeding GitHub's 100 MiB per-file limit. Its exact bytes are stored in the four ordered files in `source-chunks/`; `source-chunks.json` records every chunk's size and SHA256 and the original archive's size and SHA256. Only the reconstructed `source.tar.gz` is ignored by the archive-local `.gitignore`.

From the repository root, reconstruct and verify it with:

```sh
python3 docs/theorem18/landmarks/github-evidence/run-43599459363/reassemble-source.py
```

The streaming reassembler checks every chunk and the complete archive before publishing the output. An identical existing output is accepted; a conflicting existing output is refused. Use `--output /path/to/source.tar.gz` to choose another destination.

The authoritative original archive SHA256 is `9c4a9d49d85ebe80ab7359c177e774c3c807474261900eb2b637f8b3d4b63423`. Original `archive-verification.json`, `SHA256SUMS`, README, ZIP, logs and source records are preserved unchanged. This transport step performs no Lean compilation or proof replay. `source-reassembly-verification.json` records the actual successful reconstruction to a temporary destination.
