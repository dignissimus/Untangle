ARG VARIANT="jammy"
FROM mcr.microsoft.com/vscode/devcontainers/base:0-${VARIANT}

RUN apt-get update && apt-get install -yq build-essential nodejs npm

USER vscode
RUN echo $HOME
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSfL | sh -s -- --default-toolchain leanprover/lean4:nightly -y
RUN echo 'export PATH="$HOME/.elan/bin:$PATH"' >> $HOME/.profile
