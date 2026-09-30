# web3signer_bend for devnets. Build the binary first (scripts/build.sh), then run
# this from the repository root:
#
#   docker build -f docker/Dockerfile -t web3signer_bend:local .
#
# The binary links OpenSSL and ICU dynamically, so the image uses the same
# distribution as the build host (Arch Linux).
FROM archlinux:latest
RUN pacman -Sy --noconfirm --needed openssl icu socat && pacman -Scc --noconfirm
COPY build/web3signer_bend /usr/local/bin/web3signer_bend
COPY docker/entrypoint.sh /usr/local/bin/web3signer_bend-entrypoint
ENTRYPOINT ["/usr/local/bin/web3signer_bend-entrypoint"]
