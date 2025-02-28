#!/bin/bash

# Anonymize the patches

sed -i 's/^From: .*/From: anon <anon>/' *.patch
sed -i '/^From [0-9a-f]\{40\}/d' *.patch
sed -i '/^index [0-9a-f]*\.\.[0-9a-f]* /d' *.patch
sed -i '/^Date: /d' *.patch
