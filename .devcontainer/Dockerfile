FROM docker.io/library/elixir:1.19-alpine

RUN apk add --no-cache \
    nodejs \
    npm \
    git \
    curl \
    zsh \
    sudo \
    ripgrep \
    fd \
    ncurses-terminfo-base

RUN npm install -g @anthropic-ai/claude-code
RUN curl -LsSf https://ast-grep.github.io/install.sh | sh

RUN adduser -D node && echo "node ALL=(ALL) NOPASSWD:ALL" > /etc/sudoers.d/node
USER node
WORKDIR /workspace

ENV SHELL=/bin/zsh