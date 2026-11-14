#!/usr/bin/env python3
"""Verify and stream the exact archived source snapshot from lossless chunks."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Destination; defaults to source.tar.gz beside this script')
    args = parser.parse_args()
    archive = Path(__file__).resolve().parent
    manifest_path = archive / 'source-chunks.json'
    manifest = json.loads(manifest_path.read_text())
    assert manifest['schema_version'] == 1
    assert manifest['original_filename'] == 'source.tar.gz'
    output = args.output if args.output is not None else archive / manifest['original_filename']
    output = output.absolute()
    output.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix='.source-reassembly-', dir=output.parent)
    temporary = Path(temporary)
    full_hash = hashlib.sha256()
    total = 0
    try:
        with os.fdopen(fd, 'wb') as target:
            for index, chunk in enumerate(manifest['chunks']):
                expected_name = f'source-chunks/source.tar.gz.part{index:03d}'
                if chunk['path'] != expected_name:
                    raise ValueError(f'Unexpected chunk path: {chunk["path"]}')
                chunk_hash = hashlib.sha256()
                chunk_size = 0
                with (archive / expected_name).open('rb') as source:
                    while block := source.read(1024 * 1024):
                        chunk_hash.update(block)
                        full_hash.update(block)
                        target.write(block)
                        chunk_size += len(block)
                        total += len(block)
                if chunk_size != chunk['size_bytes'] or chunk_hash.hexdigest() != chunk['sha256']:
                    raise ValueError(f'Chunk size or digest mismatch: {expected_name}')
        if total != manifest['original_size_bytes'] or full_hash.hexdigest() != manifest['original_sha256']:
            raise ValueError('Reassembled archive size or digest mismatch')
        # An exclusive hard link publishes the complete verified file without replacing anything.
        try:
            os.link(temporary, output)
            status = 'reconstructed'
        except FileExistsError:
            if output.stat().st_size != total or digest(output) != full_hash.hexdigest():
                raise FileExistsError(f'Refusing conflicting existing output: {output}')
            status = 'existing-identical'
        print(json.dumps({'ok': True, 'status': status, 'output': str(output),
                          'size_bytes': total, 'sha256': full_hash.hexdigest(),
                          'chunks_verified': len(manifest['chunks'])}))
    finally:
        temporary.unlink(missing_ok=True)


if __name__ == '__main__':
    main()
