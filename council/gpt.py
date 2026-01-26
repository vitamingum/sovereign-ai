#!/usr/bin/env python3
"""GPT CLI - thin wrapper"""
from client import GPTClient, cli_main

if __name__ == "__main__":
    cli_main(GPTClient)
