# to use this, build with `docker build -t compilers .`
# run with `docker run -it compilers` 

FROM ubuntu:bionic

# execute build commands using bash (as a login shell)
SHELL ["/bin/bash", "-cl"]

# install apt deps
RUN apt update && apt upgrade && \ 
    apt install -y sudo git curl build-essential clang nasm valgrind vim patch unzip bubblewrap m4 && \
    apt clean
# install brew and opam
RUN yes "" | /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)" && \
    echo 'eval "$(/home/linuxbrew/.linuxbrew/bin/brew shellenv)"' >> /root/.profile && \
    eval "$(/home/linuxbrew/.linuxbrew/bin/brew shellenv)" && \
    brew install opam
# create the docker user and set docker/root user passwords to "docker"
RUN useradd -s /bin/bash -m docker && printf "docker:docker\nroot:docker" | chpasswd && adduser docker sudo

# main user is now docker
USER docker
WORKDIR /home/docker

# the default program that runs when starting a container
ENTRYPOINT ["/bin/bash", "-c"]
CMD ["/bin/bash"]

# set up brew for docker user and initialize opam
RUN echo 'eval "$(/home/linuxbrew/.linuxbrew/bin/brew shellenv)"' >> ~/.bashrc && \
    eval "$(/home/linuxbrew/.linuxbrew/bin/brew shellenv)" && \
    opam init -y && echo "eval \`opam config env\`" >> ~/.bashrc && \
    echo ". /home/docker/.opam/opam-init/init.sh" >> ~/.bashrc && \
    echo "export OUNIT_CI=true" >> ~/.bashrc && \
    source ~/.bashrc && opam switch create 4.13.1 

# install opam deps
RUN eval "$(/home/linuxbrew/.linuxbrew/bin/brew shellenv)" && \
    opam install -y extlib ounit batteries utop

# copy in code to /home/compilers/
COPY . /home/docker/compilers
