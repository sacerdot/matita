#!/bin/sh

sed -i 's/Mk_any_status((Matita_freescale_status/Mk_any_status(Obj.magic(Matita_freescale_status/g' *.ml
sed -i 's/match alu with/match (Obj.magic alu) with/g' *.ml

