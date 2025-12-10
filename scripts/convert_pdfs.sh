#!/bin/bash
# This script converts all PDF files in the ../refs directory to text files.

set -e

REFS_DIR=$(dirname "$0")/../refs

for pdf_file in "$REFS_DIR"/*.pdf; do
  if [ -f "$pdf_file" ]; then
    txt_file="${pdf_file%.pdf}.txt"
    echo "Converting $pdf_file to $txt_file..."
    pdftotext "$pdf_file" "$txt_file"
  fi
done

echo "Conversion complete."
