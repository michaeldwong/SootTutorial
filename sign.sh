#!/bin/bash -e

# This is used to sign apk prior to Android emulator installation

if ! [ "$1" ]; then
    echo "usage: $0 <original.apk>"
    exit -1
fi

apk=$1
echo "$apk"
apksigner sign --ks ~/.android/release-key.keystore $apk 
