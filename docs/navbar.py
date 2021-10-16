import sys

from bs4 import BeautifulSoup

soup = BeautifulSoup("".join(sys.stdin.readlines()), "html.parser")
print(soup.prettify())
