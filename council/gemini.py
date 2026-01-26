#!/usr/bin/env python3
"""Gemini CLI - thin wrapper"""
from client import GeminiClient, cli_main

if __name__ == "__main__":
    cli_main(GeminiClient)
