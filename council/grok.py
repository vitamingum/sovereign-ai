#!/usr/bin/env python3
"""Grok CLI - thin wrapper"""
from client import GrokClient, cli_main

if __name__ == "__main__":
    cli_main(GrokClient)
