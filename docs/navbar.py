import sys

from bs4 import BeautifulSoup

LINKS = [("home", "index.html"), ("guide", "guide.html"), ("quick reference", "quick-reference.html")]

soup = BeautifulSoup("".join(sys.stdin.readlines()), "html.parser")

navbar = soup.new_tag("navbar")
navbar_list = soup.new_tag("ul")
navbar.append(navbar_list)

for text, href in LINKS:
    list_item = soup.new_tag("li")
    link = soup.new_tag("a", href=href)
    link.string = text
    list_item.append(link)
    navbar_list.append(list_item)

soup.html.body.insert(0, navbar)

print(soup.prettify())
