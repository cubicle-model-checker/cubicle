import pandas as pd
import pydtmc as mc
import matplotlib.pyplot as plt
#import networkx as nx
import sys
#import lxml


args = sys.argv

if len(args) < 2:
    raise ValueError("Missing command line argument: please specify a log file.")

filename = args[1]


df = pd.read_csv(filename, sep=':', names=['transition', 'counts'])
df[['source', 'target']] = df['transition'].str.split('->', expand=True)


df['counts'] = df['counts'].astype(float)

matrix = pd.pivot_table(df, values='counts', index='source', columns='target', fill_value=0)


sum_by_source = df.groupby('source')['counts'].sum()
#print(sum_by_source)


df['prob'] = df.apply(lambda x: 0.0 if sum_by_source[x['source']] == 0.0 else x['counts'] / sum_by_source[x['source']], axis=1)

#print(df)



final_matrix = pd.pivot_table(df, values='prob', index='source', columns='target')

arr = final_matrix.values
index = final_matrix.index.tolist()

#print(final_matrix.values)

print(final_matrix.to_markdown(tablefmt="grid"))
#final_matrix.to_xml('foo.xml')
#print(final_matrix.to_markdown())


'''Markov'''

#markov = mc.MarkovChain(arr,['t', 't1', 't2', 't4'])
markov = mc.MarkovChain(arr,index)
print(markov)
print(markov.steady_states)

#mc.plot_eigenvalues(markov, dpi=150)
#mc.plot_graph(markov, dpi=300)
#plt.show()

