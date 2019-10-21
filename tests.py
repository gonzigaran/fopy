# -*- coding: utf-8 -*-
# !/usr/bin/env python

import fopy

def main():
    model = fopy.parser("fopy/model-examples/algebra.model")
    print(model)
    
if __name__ == "__main__":
    main()
