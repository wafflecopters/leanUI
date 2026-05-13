/**
 * Source-level compiler directives parsed before normal declaration parsing.
 */

/**
 * Parse @assumeK directive from source code.
 *
 * Recognizes (with or without -- prefix):
 *   @assumeK         (equivalent to @assumeK=true)
 *   @assumeK=true
 *   @assumeK=false
 *
 * @returns true if @assumeK or @assumeK=true, false if @assumeK=false, undefined if not present
 */
export function parseAssumeKDirective(source: string): boolean | undefined {
  const lines = source.split('\n');
  for (const line of lines) {
    const trimmed = line.trim();
    const match = trimmed.match(/^(?:--\s*)?@assumeK(?:=(\w+))?/);
    if (!match) continue;

    const value = match[1];
    if (!value || value === 'true') return true;
    if (value === 'false') return false;

    // Warning instead of throw for incomplete/invalid directive
    console.warn(
      `Warning: Invalid @assumeK directive value '${value}'. Expected 'true' or 'false'. Treating as 'false'.`,
    );
    return false;
  }
  return undefined;
}
