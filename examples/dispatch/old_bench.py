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
      width: 15%;
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
      align-items: center;
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
        <th class="invariants"><div>Invariants</div></th>
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
        table_html += f"    <td class='states'>{fields[3].split(':')[1].strip()}</td>\n"
        table_html += f"    <td class='nodes'>{fields[4].split(':')[1].strip()}</td>\n"        
        table_html += f"    <td class='options'>{fields[6].split(':')[1].strip()}</td>\n"
        table_html += f"    <td class='states'>{fields[7].split(':')[1].strip()}</td>\n"        
        table_html += f"    <td class='nodes'>{fields[8].split(':')[1].strip()}</td>\n"
        table_html += f"    <td style='text-align: center;'>{fields[9].split(':')[1].strip()}</td>\n"
        table_html += "  </tr>\n"

    table_html += "</table>"

    return table_html

# Read the content of the TXT file
with open('dispatch_bench.txt', 'r') as file:
    content = file.read()

# Split the content into individual entries
entries = content.strip().split('\n\n')

# Generate the HTML table
html_table = generate_html_table(entries)

# Save the HTML table to a new file
with open('dispatch_bench.html', 'w') as file:
    file.write(html_table)
