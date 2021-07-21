# js_viewer
## Updating, Installing

A graph viwer was integrated for cubicle. You can find the sources of the viewer here: [emilienlemaire/js_viewer](https://github.com/emilienlemaire/js_viewer).

To update the viewer please copy the built bundle into this folder under the name `js_viewer.js`.

Then you can build and reinstall Cubicle with `./configure && make && make install`.

## Usage

There a few update to the flags of cubcile to enable the viewer.
Here is a table describing the changes and additions to the options of cubicle.

| Flag                | Changes                                                                                                                            | Additions                                                                                                                                                                                                                                          |
| ----                | -------                                                                                                                            | ---------                                                                                                                                                                                                                                          |
| `-dot <number>`     | This flag now only generates a .dot file with the same graph as before in it. **It must be used before the other described flags** | None                                                                                                                                                                                                                                               |
| `-html`             | New                                                                                                                                | This flags generates an .html file that you can open to use js_viewer on the generated graph. The js_viwer source code is copied inside the .html file, so you can share it with people who don;t have cubicle or js_viewer installed and offline. |
| `-html-online`      | New                                                                                                                                | This flags generale a .html file that sources cubicle from an online cdn. This enables smaller files but requires a network connection to work.                                                                                                    |
| `-pdf`              | New                                                                                                                                | This flags generates the old pdf view of the graph from previous cubicle versions.                                                                                                                                                                 |
| `-js_viewer <path>` | New                                                                                                                                | This flags enables to give a custom path to js_viewer, so if you don't have it installed or you wnat to try another version than the installed one, you can provide your custom path.                                                              |

## Contributing

If you wish to contribute to js_viewer, please check the js_viewer repository: [emilienlemaire/js_viewer](https://github.com/emilienlemaire/js_viewer)
