/**
 * Groups source code into logical blocks based on indentation.
 *
 * Rules:
 * 1. `inductive` keyword starts a block that ends at blank line or EOF
 * 2. Otherwise, first non-indented line is the signature
 * 3. Subsequent non-indented lines are pattern clauses
 * 4. Indented lines belong to the previous non-indented line
 * 5. Blank lines end the current block
 * 6. Comments are handled: they don't affect indentation grouping
 */

export interface SourceBlock {
  lines: string[];      // Raw source lines (including indented continuations)
  startLine: number;    // Starting line number (1-indexed)
  isInductive: boolean; // True if this is an inductive definition
  isComment?: boolean;  // True if this is a standalone comment block
}

/**
 * Check if a line is blank (only whitespace)
 * A line with only a comment is NOT considered blank
 */
function isBlankLine(line: string): boolean {
  return /^\s*$/.test(line);
}

/**
 * Check if a line starts with a comment (ignoring leading whitespace)
 */
function isCommentLine(line: string): boolean {
  const trimmed = line.trim();
  return trimmed.startsWith('--') || trimmed.startsWith('/-') || trimmed.startsWith('{-');
}

/**
 * Classify a line's content type
 */
type LineType =
  | { type: 'blank' }
  | { type: 'line-comment'; isStandalone: boolean }  // isStandalone = no code before --
  | { type: 'block-comment-start'; isStandalone: boolean }
  | { type: 'block-comment-content' }
  | { type: 'block-comment-end'; hasMoreContent: boolean }
  | { type: 'code' };

/**
 * Determine the type of a line, considering block comment state.
 *
 * @param line - The line to classify
 * @param inBlockComment - Whether we're currently inside a block comment
 * @returns The line type classification
 */
function classifyLine(line: string, inBlockComment: boolean): LineType {
  // Blank line
  if (isBlankLine(line)) {
    return { type: 'blank' };
  }

  // Already in block comment
  if (inBlockComment) {
    // Check if this line ends the block comment
    if (line.includes('-}')) {
      const afterClose = line.substring(line.indexOf('-}') + 2);
      const hasMoreContent = afterClose.trim().length > 0 && !afterClose.trim().startsWith('--');
      return { type: 'block-comment-end', hasMoreContent };
    }
    return { type: 'block-comment-content' };
  }

  const trimmed = line.trim();

  // Check for single-line block comment (starts and ends on same line)
  if (trimmed.startsWith('{-') && line.includes('-}')) {
    const startIdx = line.indexOf('{-');
    const endIdx = line.indexOf('-}', startIdx);
    if (endIdx > startIdx) {
      // Single-line block comment
      const beforeOpen = line.substring(0, startIdx).trim();
      const afterClose = line.substring(endIdx + 2).trim();
      const isStandalone = beforeOpen.length === 0;
      const hasMoreContent = afterClose.length > 0 && !afterClose.startsWith('--');

      // Treat as block-comment-end for simplicity
      return { type: 'block-comment-end', hasMoreContent };
    }
  }

  // Check for block comment start (multiline)
  if (trimmed.startsWith('{-')) {
    const beforeOpen = line.substring(0, line.indexOf('{-')).trim();
    const isStandalone = beforeOpen.length === 0;
    return { type: 'block-comment-start', isStandalone };
  }

  // Check for line comment
  if (trimmed.startsWith('--')) {
    return { type: 'line-comment', isStandalone: true };
  }

  // Check for inline line comment (code before --)
  if (line.includes('--')) {
    const beforeComment = line.substring(0, line.indexOf('--')).trim();
    if (beforeComment.length > 0) {
      return { type: 'line-comment', isStandalone: false };
    }
    return { type: 'line-comment', isStandalone: true };
  }

  // Otherwise it's code
  return { type: 'code' };
}

/**
 * Check if a line is indented (starts with whitespace)
 * Comment-only lines are treated as indented (continuations)
 */
function isIndented(line: string): boolean {
  if (isBlankLine(line)) return false;
  if (isCommentLine(line)) return true; // Treat comments as continuations
  return /^\s/.test(line);
}

/**
 * Group source code into logical blocks by indentation.
 *
 * @param source - The source code to parse
 * @returns Array of source blocks
 */
export function groupByIndentation(source: string): SourceBlock[] {
  const lines = source.split('\n');
  const blocks: SourceBlock[] = [];
  let currentBlock: string[] = [];
  let blockStartLine = 1;
  let inBlock = false;
  let isInductiveBlock = false;
  let isCommentBlock = false;
  let inBlockComment = false;
  let pendingAttachedComments: string[] = [];  // Comments waiting to be attached
  let pendingCommentsStartLine = 1;

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    const lineNumber = i + 1;
    const lineType = classifyLine(line, inBlockComment);

    // Track block comment state
    if (lineType.type === 'block-comment-start') {
      inBlockComment = true;
    } else if (lineType.type === 'block-comment-end') {
      inBlockComment = false;
    }

    // Blank lines end the current block (unless we're inside a block comment)
    if (lineType.type === 'blank') {
      if (inBlockComment) {
        // We're inside a block comment, keep this blank line as part of it
        if (isCommentBlock) {
          currentBlock.push(line);
        }
        continue;
      }

      // Blank line after pending attached comments means they're standalone
      if (pendingAttachedComments.length > 0) {
        blocks.push({
          lines: pendingAttachedComments,
          startLine: pendingCommentsStartLine,
          isInductive: false,
          isComment: true
        });
        pendingAttachedComments = [];
      }

      // Not in a block comment, so blank line ends current block
      if (currentBlock.length > 0) {
        blocks.push({
          lines: currentBlock,
          startLine: blockStartLine,
          isInductive: isInductiveBlock,
          isComment: isCommentBlock
        });
        currentBlock = [];
        inBlock = false;
        isInductiveBlock = false;
        isCommentBlock = false;
      }
      continue;
    }

    // Handle standalone comments
    if (lineType.type === 'line-comment' && lineType.isStandalone) {
      // Line comment - could be standalone or part of code block
      if (inBlock && isCommentBlock) {
        // Continue comment block
        currentBlock.push(line);
      } else if (inBlock && !isCommentBlock) {
        // We're in a code block - treat this comment as part of it
        // (it's documentation for the code)
        currentBlock.push(line);
      } else {
        // Not in any block - add to pending attached comments
        if (pendingAttachedComments.length === 0) {
          pendingCommentsStartLine = lineNumber;
        }
        pendingAttachedComments.push(line);
      }
      continue;
    }

    // Handle standalone block comments
    if (lineType.type === 'block-comment-start' && lineType.isStandalone) {
      // Start standalone block comment
      if (currentBlock.length > 0 && !isCommentBlock) {
        blocks.push({
          lines: currentBlock,
          startLine: blockStartLine,
          isInductive: isInductiveBlock,
          isComment: false
        });
        currentBlock = [];
        inBlock = false;
        isCommentBlock = false;
        isInductiveBlock = false;
      }

      // Add to pending attached comments
      if (pendingAttachedComments.length === 0) {
        pendingCommentsStartLine = lineNumber;
      }
      pendingAttachedComments.push(line);
      continue;
    }

    if (lineType.type === 'block-comment-content') {
      // Continue block comment
      if (isCommentBlock) {
        currentBlock.push(line);
      } else if (pendingAttachedComments.length > 0) {
        // Building up a pending attached block comment
        pendingAttachedComments.push(line);
      }
      continue;
    }

    if (lineType.type === 'block-comment-end') {
      // End block comment (or single-line block comment)
      if (!inBlockComment) {
        // Single-line block comment: {- ... -}
        if (currentBlock.length > 0 && !isCommentBlock) {
          // End current code block
          blocks.push({
            lines: currentBlock,
            startLine: blockStartLine,
            isInductive: isInductiveBlock,
            isComment: false
          });
          currentBlock = [];
          inBlock = false;
          isCommentBlock = false;
          isInductiveBlock = false;
        }

        // Add to pending attached comments (might be attached to next line)
        if (pendingAttachedComments.length === 0) {
          pendingCommentsStartLine = lineNumber;
        }
        pendingAttachedComments.push(line);
        continue;
      }

      // Multi-line block comment ending
      if (isCommentBlock) {
        currentBlock.push(line);
        if (!lineType.hasMoreContent) {
          // Block comment ends here, could have more after blank line
          // Keep the block open for now
        }
      } else if (pendingAttachedComments.length > 0) {
        // Ending a pending attached block comment
        pendingAttachedComments.push(line);
      }
      continue;
    }

    // Handle code lines (including lines with inline comments)
    if (lineType.type === 'code' || (lineType.type === 'line-comment' && !lineType.isStandalone)) {
      // End comment block if we were in one
      if (isCommentBlock) {
        blocks.push({
          lines: currentBlock,
          startLine: blockStartLine,
          isInductive: false,
          isComment: true
        });
        currentBlock = [];
        inBlock = false;
        isCommentBlock = false;
      }

      // Check if line is indented
      const indented = isIndented(line);

      if (!indented) {
        // Non-indented code line - attach any pending comments
        const trimmed = line.trim();

        // Check if it's an inductive definition
        if (trimmed.startsWith('inductive ')) {
          // Start new inductive block
          if (currentBlock.length > 0) {
            blocks.push({
              lines: currentBlock,
              startLine: blockStartLine,
              isInductive: isInductiveBlock,
              isComment: false
            });
          }

          // Include any pending attached comments
          if (pendingAttachedComments.length > 0) {
            currentBlock = [...pendingAttachedComments, line];
            blockStartLine = pendingCommentsStartLine;
            pendingAttachedComments = [];
          } else {
            currentBlock = [line];
            blockStartLine = lineNumber;
          }

          inBlock = true;
          isInductiveBlock = true;
          isCommentBlock = false;
        } else {
          // Regular definition line
          if (inBlock && !isInductiveBlock) {
            // This is a pattern clause for the current block
            currentBlock.push(line);
          } else {
            // Start new block
            if (currentBlock.length > 0) {
              blocks.push({
                lines: currentBlock,
                startLine: blockStartLine,
                isInductive: isInductiveBlock,
                isComment: false
              });
            }

            // Include any pending attached comments
            if (pendingAttachedComments.length > 0) {
              currentBlock = [...pendingAttachedComments, line];
              blockStartLine = pendingCommentsStartLine;
              pendingAttachedComments = [];
            } else {
              currentBlock = [line];
              blockStartLine = lineNumber;
            }

            inBlock = true;
            isInductiveBlock = false;
            isCommentBlock = false;
          }
        }
      } else {
        // Indented code line - belongs to current block
        if (inBlock && !isCommentBlock) {
          currentBlock.push(line);
        }
        // If not in a code block, skip this line (it's a stray indented line)
      }
    }
  }

  // Don't forget last block
  if (currentBlock.length > 0) {
    blocks.push({
      lines: currentBlock,
      startLine: blockStartLine,
      isInductive: isInductiveBlock,
      isComment: isCommentBlock
    });
  }

  // Don't forget pending attached comments (if they weren't attached to anything)
  if (pendingAttachedComments.length > 0) {
    blocks.push({
      lines: pendingAttachedComments,
      startLine: pendingCommentsStartLine,
      isInductive: false,
      isComment: true
    });
  }

  return blocks;
}

/**
 * Parse a source block into signature + pattern clauses.
 *
 * Returns:
 * - signature: The first non-indented line (with continuation lines joined)
 * - clauses: Array of pattern clause lines (each with their continuations joined)
 */
export interface ParsedBlock {
  signature: string;
  clauses: string[];
}

export function parseBlock(block: SourceBlock): ParsedBlock {
  if (block.isInductive) {
    // For inductive, the whole thing is the signature
    return {
      signature: block.lines.join('\n'),
      clauses: []
    };
  }

  // Group lines: first non-indented line + its continuations is signature,
  // subsequent non-indented lines + their continuations are clauses
  const groups: string[][] = [];
  let currentGroup: string[] = [];

  for (const line of block.lines) {
    if (isIndented(line)) {
      // Continuation line
      currentGroup.push(line);
    } else {
      // New group
      if (currentGroup.length > 0) {
        groups.push(currentGroup);
      }
      currentGroup = [line];
    }
  }

  // Don't forget last group
  if (currentGroup.length > 0) {
    groups.push(currentGroup);
  }

  // First group is signature, rest are clauses
  const signature = groups.length > 0 ? groups[0].join('\n') : '';
  const clauses = groups.slice(1).map(g => g.join('\n'));

  return {
    signature,
    clauses
  };
}
