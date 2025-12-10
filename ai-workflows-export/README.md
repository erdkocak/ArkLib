# AI Workflows for Lean Projects

This directory contains reusable GitHub Actions for AI-assisted development.

## Available Actions

### 1. Gemini PR Summary (`pr-summary`)

Generates a concise summary of a Pull Request using Gemini and posts it as a comment. It also tracks `sorry` (missing proofs) in Lean files.

**Usage:**

```yaml
steps:
  - uses: actions/checkout@v4
    with:
      fetch-depth: 0 # Required for diff generation

  - name: Generate PR Summary
    uses: ./ai-workflows-export/pr-summary  # Or owner/repo/pr-summary@main if moved
    with:
      gemini-api-key: ${{ secrets.GEMINI_API_KEY }}
      github-token: ${{ secrets.GITHUB_TOKEN }}
```

### 2. Gemini Code Review (`review`)

Performs an AI code review with optional external context (URLs) and repository context (local files).

**Usage:**

```yaml
steps:
  - uses: actions/checkout@v4

  - name: Run AI Review
    uses: ./ai-workflows-export/review
    with:
      gemini-api-key: ${{ secrets.GEMINI_API_KEY }}
      github-token: ${{ secrets.GITHUB_TOKEN }}
      pr-number: ${{ github.event.issue.number }}
      # Optional inputs
      external-refs: "https://example.com/paper.pdf"
      repo-refs: "src/file.lean,src/dir/"
      additional-comments: "Focus on performance."
```
