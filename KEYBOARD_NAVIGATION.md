# Keyboard Navigation System

## Overview

The Lean UI now has a complete keyboard navigation system that allows you to control the entire interface without using a mouse.

## Input Modes

The system has two modes:

1. **Navigation Mode** (default) - Navigate between sections and execute commands
2. **Typing Mode** - Edit text in inputs/editors

### Switching Modes

- Press `ESC` from any input field → Enter Navigation Mode
- Press `ESC ESC` → Clear navigation context and return to root
- Commands that open editors → Automatically switch to Typing Mode

## Navigation Commands

### Root Level (Navigation Mode, Empty Context)

| Key | Action | Description |
|-----|--------|-------------|
| `h` | Focus Hypotheses | Navigate to the Hypotheses section |
| `g` | Focus Goals | Navigate to the Goals section |
| `l` | Focus Let Bindings | Navigate to the Let Bindings section |
| `ESC` | Clear Context | Return to root navigation |

### Goals Section Commands

After pressing `g`, you're in the Goals section. Available commands:

| Key | Action | Description |
|-----|--------|-------------|
| `e` | Edit Goal | Edit the current goal |
| `s` | Set Goal | Clear and set a new goal |
| `r` | Remove Goal | Clear the goal without opening editor |
| `ESC` | Back | Return to root navigation |

Example: `ESC ESC g e` → Edit the goal (from anywhere)

### Hypotheses Section Commands

After pressing `h`, you're in the Hypotheses section. Available commands:

| Key | Action | Description |
|-----|--------|-------------|
| `a` | Add Hypothesis | Add a new hypothesis |
| `e` | Edit Hypothesis | Edit selected hypothesis (if one is selected) |
| `d` | Delete Hypothesis | Delete selected hypothesis (if one is selected) |
| `ESC` | Back | Return to root navigation |

Example: `ESC ESC h a` → Add a hypothesis (from anywhere)

### Let Bindings Section Commands

After pressing `l`, you're in the Let Bindings section. Available commands:

| Key | Action | Description |
|-----|--------|-------------|
| `a` | Add Let Binding | Add a new let binding |
| `e` | Edit Let Binding | Edit selected let binding (if one is selected) |
| `d` | Delete Let Binding | Delete selected let binding (if one is selected) |
| `ESC` | Back | Return to root navigation |

## Visual Feedback

### Footer

The footer at the bottom of the screen shows:
- **Mode Badge**: "Navigation" (blue) or "Typing" (green)
- **Context Breadcrumb**: e.g., "Navigation > Goals > Editor"
- **Available Commands**: Keyboard shortcuts you can use in the current context

### Section Focus

When you navigate to a section:
- The section gets a **blue outline** (3px solid #2845a7)
- A **label badge** appears at the top showing the section name
- The section is automatically scrolled into view and focused

## Example Workflows

### Setting a New Goal

```
ESC ESC g s
```
1. `ESC ESC` - Clear any context, enter navigation mode
2. `g` - Focus on Goals section
3. `s` - Set new goal (opens editor in typing mode)

### Editing a Hypothesis

```
ESC ESC h
[click on a hypothesis to select it]
e
```
1. `ESC ESC` - Clear context
2. `h` - Focus on Hypotheses section
3. Select a hypothesis (currently by clicking)
4. `e` - Edit the selected hypothesis

### Clearing the Current Goal

```
ESC ESC g r
```
1. `ESC ESC` - Clear context
2. `g` - Focus Goals
3. `r` - Remove/clear the goal

## Architecture

### Files Created

- **`src/types/commands.ts`** - Command system types and utilities
- **`src/contexts/NavigationContext.tsx`** - Global navigation state management
- **`src/components/NavigationFooter.tsx`** - Footer component showing navigation state
- **`src/components/FocusableSection.tsx`** - Wrapper for keyboard-focusable sections
- **`src/config/navigationCommands.ts`** - Application command tree definition

### Files Modified

- **`src/components/EnhancedProofWorkspace.tsx`** - Wrapped with NavigationProvider
- **`src/components/LetManager.tsx`** - Sections wrapped with FocusableSection

## Extending the System

### Adding New Commands

Edit `src/config/navigationCommands.ts`:

```typescript
createCommand(
  'my-command-id',
  'k',  // keyboard key
  'My Action',  // display label
  (context) => {
    // Execute action
    const myHandler = context.metadata?.myHandler as (() => void) | undefined;
    myHandler?.();

    return {
      navigationPath: ['Section', 'Subsection'],  // optional
      mode: 'typing',  // optional
      preventDefault: true,
    };
  },
  {
    description: 'Description shown in footer',
    isAvailable: (ctx) => {
      // Optional: only show when condition is met
      return ctx.metadata?.someCondition === true;
    },
  }
)
```

### Adding New Sections

1. Wrap your section in `FocusableSection`:
   ```tsx
   <FocusableSection sectionId="mysection" label="My Section">
     {/* section content */}
   </FocusableSection>
   ```

2. Add section navigation command in `navigationCommands.ts`:
   ```typescript
   createSectionCommand(
     'nav-mysection',
     'm',  // key to navigate to section
     'My Section',
     'My Section',
     {
       description: 'Navigate to my section',
       children: createMySectionCommands(),  // sub-commands
     }
   )
   ```

## TODO: Implementation Tasks

The command handlers are currently console.log stubs. To complete the integration:

1. **Connect to existing UI state** in `EnhancedProofWorkspace.tsx`:
   - `handleEditGoalCommand` → Toggle `showEditGoal` state
   - `handleSetGoalCommand` → Clear goal and toggle `showEditGoal`
   - `handleAddHypothesisCommand` → Toggle `showAddHypothesis` state
   - etc.

2. **Add selection tracking**:
   - Track `selectedHypothesisId` in state
   - Track `selectedLetBindingId` in state
   - Update metadata when selection changes

3. **Add item navigation** (optional):
   - `j` / `k` to navigate between hypotheses
   - `j` / `k` to navigate between let bindings
   - Arrow keys for finer control

## Notes

- The system prevents keyboard shortcuts from triggering when you're typing in an input field (except ESC)
- Modal support is built-in via the modal stack in NavigationContext
- All sections route focus changes through the unified navigation controller
- The footer doesn't obscure content (padding is added automatically)
