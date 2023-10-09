# -*- coding: utf-8 -*-
#

extensions = [
    'breathe',
    'exhale',
    'sphinx_rtd_theme',
]

breathe_projects = {"Sentry": "../doxygen/xml"}
breathe_default_project = "Sentry"

exhale_args = {
    "containmentFolder": "./api",
    "rootFileName": "index.rst",
    "rootFileTitle": "Sentry detailed documentation",
    "doxygenStripFromPath": ".",
    "createTreeView": True,
    "exhaleExecutesDoxygen": True,
    "exhaleUseDoxyfile": True,
}

# Add any paths that contain templates here, relative to this directory.
templates_path = ['_templates']
source_suffix = '.rst'
source_encoding = 'utf-8-sig'

# The master toctree document.
master_doc = 'index'

# General information about the project.
project = u'sentry'
copyright = u'2023, Ledger SA'
author = u'Ledger'

# The version info for the project you're documenting, acts as replacement for
# |version| and |release|, also used in various other places throughout the
# built documents.
#
# The short X.Y version.
version = u'1.0.0'
# The full version, including alpha/beta/rc tags.
release = u'1.0.0'

language = None
today_fmt = '%B %d, %Y'

# List of patterns, relative to source directory, that match files and
# directories to ignore when looking for source files.
# This patterns also effect to html_static_path and html_extra_path
exclude_patterns = []


# The name of the Pygments (syntax highlighting) style to use.
pygments_style = 'sphinx'


# If true, `todo` and `todoList` produce output, else they produce nothing.
todo_include_todos = True


# -- Options for HTML output ----------------------------------------------

html_theme = 'sphinx_rtd_theme'

html_logo = ''

# html_favicon = None

html_static_path = ['_static']
# html_extra_path = []

# If not None, a 'Last updated on:' timestamp is inserted at every page
# bottom, using the given strftime format.
# The empty string is equivalent to '%b %d, %Y'.
#
# html_last_updated_fmt = None

# If true, SmartyPants will be used to convert quotes and dashes to
# typographically correct entities.
#
html_use_smartypants = True

# Custom sidebar templates, maps document names to template names.
#
# html_sidebars = {}

# Additional templates that should be rendered to pages, maps page names to
# template names.
#
# html_additional_pages = {}

# If false, no module index is generated.
#
# html_domain_indices = True

# If false, no index is generated.
#
# html_use_index = True

# If true, the index is split into individual pages for each letter.
#
# html_split_index = False

# If true, links to the reST sources are added to the pages.
#
html_show_sourcelink = False

# If true, "Created using Sphinx" is shown in the HTML footer. Default is True.
#
html_show_sphinx = False

# If true, "(C) Copyright ..." is shown in the HTML footer. Default is True.
#
# html_show_copyright = True

# If true, an OpenSearch description file will be output, and all pages will
# contain a <link> tag referring to it.  The value of this option must be the
# base URL from which the finished HTML is served.
#
# html_use_opensearch = ''

# This is the file name suffix for HTML files (e.g. ".xhtml").
# html_file_suffix = None

# Language to be used for generating the HTML full-text search index.
# Sphinx supports the following languages:
#   'da', 'de', 'en', 'es', 'fi', 'fr', 'hu', 'it', 'ja'
#   'nl', 'no', 'pt', 'ro', 'ru', 'sv', 'tr', 'zh'
#
# html_search_language = 'en'

# A dictionary with options for the search language support, empty by default.
# 'ja' uses this config value.
# 'zh' user can custom change `jieba` dictionary path.
#
# html_search_options = {'type': 'default'}

# The name of a javascript file (relative to the configuration directory) that
# implements a search results scorer. If empty, the default will be used.
#
# html_search_scorer = 'scorer.js'

# Output file base name for HTML help builder.
htmlhelp_basename = 'sentryhoc'
# One entry per manual page. List of tuples
# (source start file, name, description, authors, manual section).
man_pages = [
    (master_doc, 'Sentry', u'Sentry kernel Documentation',
     [author], 1)
]

# If true, show URL addresses after external links.
#
# man_show_urls = False

# current public version
tags.add('v1.0.0')