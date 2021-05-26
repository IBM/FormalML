#!/bin/bash

mkdir -p coq/LInt_p
cd coq/LInt_p
curl https://lipn.univ-paris13.fr/MILC/CoqLIntp/LInt_p.tgz -o LInt_p.tgz
tar xzvf LInt_p.tgz
sed -i'.bk' 's/Require\ Import\ R_compl/Require\ Import\ LInt_p\.R_compl/g' *.v

