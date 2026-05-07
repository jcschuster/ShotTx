# Claudeman Notifications

You have access to the `notify` command for sending notifications to the host machine.

## Usage

```bash
notify <type> <message>
```

Types: `complete`, `question`, `idle`, `info`

## When to Notify

**Task Completion**: When you finish a significant task or reach a milestone.

```bash
notify complete "Implemented user authentication"
```

**Questions**: When you need clarification and are waiting for user input.

```bash
notify question "Should I use JWT or session-based auth?"
```

**Info**: For non-urgent updates during long-running tasks.

```bash
notify info "Starting test suite..."
```

## Guidelines

- Use `complete` when you've finished what the user asked for
- Use `question` when you're blocked and need user input
- Keep messages concise (the host will announce them via audio)
- Don't over-notify - only for significant events

# General Engineering Directives

- Do not overengineer solutions. Write the simplest code that satisfies the requirements.
- Favor readability and maintainability over cleverness.

# Elixir & Livebook Rules

- Always follow Elixir best practices and avoid common anti-patterns.
- Do not rebind variables (do not assign to variables that already hold a value). Instead, use the pipe operator `|>` effectively or use distinct, descriptive variable names.
- Rely on pattern matching in function heads rather than complex `if/else` or `cond` statements.
- When editing `.livemd` files, ensure Elixir code blocks compile cleanly and dependencies are properly declared in the `Mix.install/2` setup cell.
