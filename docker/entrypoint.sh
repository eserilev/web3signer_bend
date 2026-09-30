#!/bin/sh
# Starts web3signer_bend with the command line of Web3Signer, as ethereum-package
# (Kurtosis) gives it:
#
#   --http-listen-port=9000 ... eth2 --network=<config.yaml>
#   --keystores-path=<dir> --keystores-passwords-path=<dir> ...
#
# Web3Signer loads each <name>.json in the keystores directory with the
# password file <name>.txt. This script writes one web3signer_bend key-config file
# for each keystore, then starts web3signer_bend. It ignores the other flags.
set -eu

port=9000
network=""
keystores=""
passwords=""
for arg in "$@"; do
  case "$arg" in
    --http-listen-port=*) port=${arg#*=} ;;
    --network=*) network=${arg#*=} ;;
    --keystores-path=*) keystores=${arg#*=} ;;
    --keystores-passwords-path=*) passwords=${arg#*=} ;;
    *) echo "web3signer_bend-entrypoint: ignoring $arg" ;;
  esac
done

if [ -z "$keystores" ] || [ -z "$passwords" ]; then
  echo "web3signer_bend-entrypoint: --keystores-path and --keystores-passwords-path are required" >&2
  exit 2
fi

keys=/tmp/web3signer_bend-keys
mkdir -p "$keys" /data
for ks in "$keystores"/*.json; do
  name=$(basename "$ks" .json)
  printf 'type: "file-keystore"\nkeyType: "BLS"\nkeystoreFile: "%s"\nkeystorePasswordFile: "%s"\n' \
    "$ks" "$passwords/$name.txt" > "$keys/$name.yaml"
done

# ethereum-package declares a metrics port and waits for it to open.
# web3signer_bend has no metrics yet: the port answers each request with an empty
# 200 response.
printf 'HTTP/1.1 200 OK\r\nContent-Length: 0\r\nConnection: close\r\n\r\n' > /tmp/metrics.http
socat TCP-LISTEN:9001,fork,reuseaddr EXEC:"/usr/bin/cat /tmp/metrics.http" &

set -- --key-config-path "$keys" --slashing-log /data/slashing.log \
  --http-listen-host 0.0.0.0 --http-listen-port "$port"
if [ -n "$network" ]; then
  set -- "$@" --network-config "$network"
fi
exec /usr/local/bin/web3signer_bend "$@"
