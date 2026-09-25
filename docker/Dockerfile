# Bulkhead for devnets. Build the binary first (scripts/build.sh), then run
# this from the repository root:
#
#   docker build -f docker/Dockerfile -t bulkhead:local .
#
# The binary links OpenSSL and ICU dynamically, so the image uses the same
# distribution as the build host (Arch Linux).
FROM archlinux:latest
RUN pacman -Sy --noconfirm --needed openssl icu socat && pacman -Scc --noconfirm
COPY build/bulkhead /usr/local/bin/bulkhead
COPY docker/entrypoint.sh /usr/local/bin/bulkhead-entrypoint
ENTRYPOINT ["/usr/local/bin/bulkhead-entrypoint"]
