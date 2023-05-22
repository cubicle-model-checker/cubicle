def generate_html_table(entries):
    table_html = '''
    <style>
    table {
      width: 100%;
      border-collapse: collapse;
    }

    th, td {
      padding: 8px;
      text-align: left;
      border-bottom: 1px solid #ddd;
    }

    th {
      background-color: #f2f2f2;
    }

    th.options, th.nodes, th.states, th.invs {
      text-align: center;
    }

    th.model {
      border-right: 1px solid #ddd;
    }

    th.forward, th.fuzz {
      text-align: center;
      padding-top: 16px;
    }

    colgroup.col-model {
      width: 20%;
    }

    colgroup.col-options,
    colgroup.col-nodes,
    colgroup.col-states,
    colgroup.col-invs {
      width: 10%;
    }

    td.options, td.nodes, td.states, td.invs {
      text-align: center;
    }

    tr:nth-child(even) {
      background-color: #f9f9f9;
    }

    tr:hover {
      background-color: #e9e9e9;
    }

    th.model,
    th.invariants {
      height: 0;
      line-height: 0;
      padding-top: 0;
      padding-bottom: 0;
      border: none;
    }

    th.model div,
    th.invariants div {
      display: flex;
      align-items: flex-end;
      justify-content: center;
      height: 100%;
    }
    
    th.model:after,
    th.invariants:after {
      content: '';
      display: block;
      height: 10px;
    }

    th:not(:first-child),
    td:not(:first-child) {
      border-left: 1px solid #ddd;
    }
    </style>
    <table>
      <colgroup>
        <col class="col-model">
        <col class="col-options">
        <col class="col-nodes">
        <col class="col-states">
        <col class="col-invs">
        <col class="col-options">
        <col class="col-nodes">
        <col class="col-states">
        <col class="col-invs">
        <col>
      </colgroup>
      <tr>
        <th class="model"><div>Model</div></th>
        <th colspan="4" class="forward">Forward</th>
        <th colspan="4" class="fuzz">Fuzz</th>
        <th class="invariants"><div>Notes</div></th>
      </tr>
      <tr>
        <th></th>
        <th class="options">Options</th>
        <th class="nodes">Nodes</th>
        <th class="states">States</th>
        <th class="invs">Invs</th>
        <th class="options">Options</th>
        <th class="nodes">Nodes</th>
        <th class="states">States</th>
        <th class="invs">Invs</th>
        <th></th>
      </tr>
    '''

    for entry in entries:
        fields = entry.strip().split('\n')
        table_html += "  <tr>\n"
        table_html += f"    <td style='text-align: center;'>{fields[0]}</td>\n"
        table_html += f"    <td class='options'>{fields[2].split(':')[1].strip()}</td>\n"
        table_html += f"    <td class='nodes'>{fields[3].split(':')[1].strip()}</td>\n"
        table_html += f"    <td class='states'>{fields[4].split(':')[1].strip()}</td>\n"
        table_html += f"    <td class='invs'>{fields[5].split(':')[1].strip()}</td>\n"
        table_html += f"    <td class='options'>{fields[7].split(':')[1].strip()}</td>\n"
        table_html += f"    <td class='nodes'>{fields[8].split(':')[1].strip()}</td>\n"
        table_html += f"    <td class='states'>{fields[9].split(':')[1].strip()}</td>\n"
        table_html += f"    <td class='invs'>{fields[10].split(':')[1].strip()}</td>\n"
        table_html += f"    <td>{fields[11].split(':')[1].strip()}</td>\n"
        table_html += "  </tr>\n"

    table_html += "</table>"
    table_html += "<p> NOTES </p>"
    table_html += "<p>[X]: Cubicle could not prove the property w/ Forward within the same number of nodes with significantly more states visited -> no point in going up </p>"
    table_html += "<p>(1) Original germanish3 deadlocks, while the dispatch version livelocks: the germanish part of the protocol deadlocks, but dispatch part can still run</p>"
    table_html += "<p>(*) Not overly stable. 500 000 states tends to work, but occasionally fails</p>"
    table_html += "<p>(2) Dispatch version generates more invariants than normal but none of the invariants contain dispatch variables</p>"
    table_html += "<p>(**) Germanish3 and Germanish4 visit 7 158 986 nodes at a depth of 20, meaning 20 is not low enough to diverge since after dispatch the algorithms are different [G3: 658(depth=12) vs G4: 966(depth=12)]</p>"
    table_html += "<p>(♦) Tried w/ depth 25, stopped at 10 759 410 states, did not work - stopped Cubicle at 151 nodes.</p>"
    table_html += "<p>(3) Dispatch version generates more invariants than normal but none of the invariants contain dispatch variables</p>"
    table_html += "<p>(4) Dispatch version generates more invariants than normal but none of the invariants contain dispatch variables</p>"

    return table_html

# Read the content of the TXT file
with open('dispatch_bench.txt', 'r') as file:
    content = file.read()

# Split the content into individual entries
entries = content.strip().split('\n\n')

# Generate the HTML table
html_table = generate_html_table(entries)

# Save the HTML table to a new file
with open('bench.html', 'w') as file:
    file.write(html_table)
