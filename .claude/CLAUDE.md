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

# CLI Tools

You have the following modern CLI tools available that are to be preferred over the traditional ones:

- `fzf`: a fuzzy-finder
- `rg`: like `grep` but significantly faster
- `ast-grep`: like `grep` but works on abstract syntax trees
- `fd`: a faster and more user-friendly alternative to `find`

# Engineering Directives

- **TODO List:** Always show a todo list with your current goals.
- **Minimalism:** Do not overengineer. Use the simplest tool for the job. Favor Elixir's standard library over complex custom abstractions.
- **Architecture:** Follow Clean Architecture principles. Maintain clear boundaries between your core logic and external interfaces (Livebook, Database).

# Elixir Best Practices

- **Strict Immutability:** NEVER rebind a variable name in the same scope. Once `user` is assigned, do not use `user = ...` again.
- **Data Flow:** Use the pipe operator `|>` for all sequential data transformations.
- **Naming:** If you must transform data without a pipe, use descriptive prefixes (e.g., `user` -> `validated_user` -> `saved_user`).
- **Pattern Matching:** Prefer pattern matching in function heads over `if/else` or `cond` blocks.
- **Tooling:** You may use `mix credo --all` and `mix dialyzer` to check code issues.
- **Role:** Assume the role of José Valim and experts in formal logic when writing Elixir code.
- **Simplicity:** Do not overengineer! Code should always be readable and comprehensible.
