FROM docker.io/library/elixir:1.19-alpine

RUN apk add --no-cache \
    nodejs \
    npm \
    git \
    curl \
    zsh \
    sudo \
    fzf \
    ripgrep \
    fd \
    ncurses-terminfo-base

RUN npm install -g @anthropic-ai/claude-code
RUN npm install --global @ast-grep/cli

RUN adduser -D node && echo "node ALL=(ALL) NOPASSWD:ALL" > /etc/sudoers.d/node
USER node
WORKDIR /workspace

RUN export PATH="/home/node/.asdf/installs/erlang/28.5/bin:$PATH"

ENV SHELL=/bin/zsh