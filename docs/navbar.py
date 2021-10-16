import sys

from bs4 import BeautifulSoup

soup = BeautifulSoup("".join(sys.stdin.readlines()), "html.parser")

# find <body>
# insert <nav class="top-bar"> with <ul>-tags

print(soup.prettify())
