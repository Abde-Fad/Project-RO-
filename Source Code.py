"""
EMI - Ecole Mohammadia d'Ingénieurs
Operational Research Desktop Application
Electrical Engineering - Morocco
Student: Fadlaoui Abd-essamade
Supervisor: Dr. EL MKHALET MOUNA

Algorithms implemented:
  Graph Algorithms: Welsh-Powell, Kruskal, Dijkstra, Bellman-Ford, Ford-Fulkerson
  Transport Methods: Nord-Ouest, Moindre Coût, Potentiel-MODI (MODI Method)
  Linear Programming: Simplex Method (user-defined variables & constraints)
"""

import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext
import math
import random
import heapq
import copy
from collections import defaultdict, deque

# ─────────────────────────────────────────────────────────────────
#  MATPLOTLIB EMBEDDING
# ─────────────────────────────────────────────────────────────────
try:
    import matplotlib
    matplotlib.use("TkAgg")
    import matplotlib.pyplot as plt
    import matplotlib.patches as mpatches
    from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
    import networkx as nx
    import numpy as np
    HAS_PLOT = True
except ImportError:
    HAS_PLOT = False

# ─────────────────────────────────────────────────────────────────
#  MOROCCAN ELECTRICAL ENGINEERING DATA
# ─────────────────────────────────────────────────────────────────
MOROCCAN_CITIES = [
    "Casablanca","Rabat","Marrakech","Fès","Tanger","Agadir",
    "Meknès","Oujda","Kenitra","Tétouan","Safi","El Jadida",
    "Béni Mellal","Nador","Mohammadia","Khouribga","Settat",
    "Laâyoune","Ksar El Kébir","Guelmim","Errachidia","Ouarzazate",
    "Taza","Tiznit","Ifrane","Chefchaouen","Al Hoceima","Taroudant"
]

MOROCCAN_SUBSTATIONS = [
    "SS-Casablanca-Ain-Chock","SS-Rabat-Agdal","SS-Marrakech-Guéliz",
    "SS-Fès-Saiss","SS-Tanger-Port","SS-Agadir-Talborjt",
    "SS-Meknès-Hamria","SS-Oujda-Bettana","SS-Kenitra-Centre",
    "SS-Tétouan-Martil","SS-Safi-Plateau","SS-El-Jadida-Centre",
    "SS-Béni-Mellal-Hay-Isly","SS-Nador-Corniche","SS-Mohammadia-Est",
    "SS-Khouribga-OCP","SS-Settat-Nord","SS-Laâyoune-Hassan-II",
    "SS-Kenitra-Naval","SS-Jorf-Lasfar","SS-Noor-Ouarzazate",
    "SS-Tensift-Marrakech","SS-Taza-Sud","SS-Tiznit-Centre"
]

PROJECTS = [
    "Noor Ouarzazate Solar Complex","Wind Farm Tarfaya",
    "Jorf Lasfar Power Plant","ONEE 400kV Backbone",
    "Mohammed VI Tangier Tech City Grid",
    "Casablanca Smart Grid Pilot","Agadir Solar Microgrid",
    "Kenitra Electric Vehicle Charging Network",
    "Tanger-Tétouan Transmission Upgrade",
    "OCP Khouribga Industrial Supply"
]

# ─────────────────────────────────────────────────────────────────
#  COLOUR PALETTE  (warm earth tones — no blue background)
# ─────────────────────────────────────────────────────────────────
C_BG        = "#F5F0E8"   # warm cream
C_PANEL     = "#EDE8DA"   # slightly darker cream
C_HEADER    = "#2C3E50"   # dark slate
C_ACCENT1   = "#C0392B"   # rich red (EMI colours)
C_ACCENT2   = "#27AE60"   # green
C_ACCENT3   = "#E67E22"   # orange
C_BTN       = "#2C3E50"   # dark button
C_BTN_TXT   = "#FFFFFF"
C_TITLE_TXT = "#FFFFFF"
C_LABEL     = "#2C3E50"
C_ENTRY_BG  = "#FFFFFF"
C_BORDER    = "#BDB5A0"

FONT_TITLE  = ("Helvetica", 18, "bold")
FONT_SUB    = ("Helvetica", 13, "bold")
FONT_BODY   = ("Helvetica", 11)
FONT_MONO   = ("Courier", 10)
FONT_BTN    = ("Helvetica", 11, "bold")
FONT_SMALL  = ("Helvetica", 9)

# ─────────────────────────────────────────────────────────────────
#  SHARED GRAPH STATE  (persists across algorithm windows)
# ─────────────────────────────────────────────────────────────────
class SharedGraph:
    """One graph shared by all algorithm modules."""
    def __init__(self):
        self.reset()

    def reset(self):
        self.nodes       = []        # list of node labels
        self.edges       = []        # list of (u, v, weight)
        self.directed    = False
        self.n_vertices  = 0
        self.density     = 50
        self.generated   = False
        self.has_negative = False    # True if any edge has a negative weight
        self.pos         = {}        # node -> (x,y) layout positions

    def generate(self, n_vertices, density, directed=False, seed=None, neg_pct=0):
        if seed is not None:
            random.seed(seed)
        self.reset()
        self.n_vertices = n_vertices
        self.density    = density
        self.directed   = directed

        # Build node name pool — Moroccan substations + cities + extras for up to 100
        extra = [
            "Midelt","Azrou","Khénifra","Zagora","Tan-Tan","Assa",
            "Smara","Dakhla","Boujdour","Essaouira","Youssoufia",
            "Fquih-Ben-Salah","Souk-el-Arba","Berkane","Taourirt",
            "Jerada","Bouarfa","Sidi-Ifni","Aït-Melloul","Biougra",
            "Chtouka","Oulad-Teima","Azilal","Afourar","Kasba-Tadla",
            "Berrechid","Benslimane","Bouznika","Temara","Skhirat",
            "Sale-Tabriquet","Ain-Harrouda","Zenata","Tit-Mellil",
            "Had-Soualem","Bouskoura","Dar-Bouazza","Nouaceur",
            "Mediouna","Lahraouyine","Zenata-Airport","Oulad-Ayad",
            "Bzou","Beni-Amir","Souk-Sebt","Bir-Jdid","Moulay-Bousselham"
        ]
        pool = list(MOROCCAN_SUBSTATIONS) + list(MOROCCAN_CITIES) + extra
        while len(pool) < n_vertices:
            pool.append(f"Node-{len(pool)+1}")
        self.nodes = pool[:n_vertices]

        max_edges = n_vertices * (n_vertices - 1) // 2
        n_edges   = max(n_vertices - 1, int(max_edges * density / 100))
        n_edges   = min(n_edges, max_edges)

        # Guarantee connectivity via a random spanning tree first
        perm = list(range(n_vertices))
        random.shuffle(perm)
        edge_set = set()
        for i in range(1, n_vertices):
            u = perm[i - 1]
            v = perm[i]
            if u > v:
                u, v = v, u
            w = random.randint(10, 500)
            edge_set.add((u, v, w))

        # Add extra edges up to n_edges
        attempts = 0
        while len(edge_set) < n_edges and attempts < 10000:
            u = random.randint(0, n_vertices - 1)
            v = random.randint(0, n_vertices - 1)
            if u != v:
                if u > v:
                    u, v = v, u
                if not any(e[0] == u and e[1] == v for e in edge_set):
                    w = random.randint(10, 500)
                    edge_set.add((u, v, w))
            attempts += 1

        self.edges = [(self.nodes[u], self.nodes[v], w) for u, v, w in edge_set]

        # Compute layout positions
        self._compute_positions()
        self.generated = True

    def _compute_positions(self):
        """Circular layout with slight jitter."""
        n = len(self.nodes)
        self.pos = {}
        for i, node in enumerate(self.nodes):
            angle = 2 * math.pi * i / max(n, 1)
            r = 1.0 + random.uniform(-0.08, 0.08)
            self.pos[node] = (r * math.cos(angle), r * math.sin(angle))

    def to_networkx(self):
        if not HAS_PLOT:
            return None
        G = nx.DiGraph() if self.directed else nx.Graph()
        G.add_nodes_from(self.nodes)
        for u, v, w in self.edges:
            G.add_edge(u, v, weight=w)
        return G

SHARED = SharedGraph()

# ─────────────────────────────────────────────────────────────────
#  UTILITY: draw graph on a matplotlib canvas
# ─────────────────────────────────────────────────────────────────
def draw_graph_on_canvas(canvas_frame, highlight_edges=None,
                         highlight_nodes=None, title="",
                         node_colors=None, figsize=(8, 5)):
    """
    Draw SHARED graph on canvas_frame (a tk Frame).
    highlight_edges : list of (u,v) tuples to colour red
    highlight_nodes : dict {node: colour}
    Returns the FigureCanvasTkAgg object.
    """
    if not HAS_PLOT or not SHARED.generated:
        lbl = tk.Label(canvas_frame,
                       text="⚠  Generate a graph first (main menu).",
                       bg=C_BG, fg=C_ACCENT1, font=FONT_BODY)
        lbl.pack(expand=True)
        return None

    # clear old widgets
    for w in canvas_frame.winfo_children():
        w.destroy()

    G   = SHARED.to_networkx()
    pos = SHARED.pos

    fig, ax = plt.subplots(figsize=figsize, facecolor=C_BG)
    ax.set_facecolor(C_BG)
    ax.axis("off")
    if title:
        ax.set_title(title, fontsize=11, fontweight="bold",
                     color=C_HEADER, pad=6)

    # default node colour
    n_colors = []
    for nd in G.nodes():
        if highlight_nodes and nd in highlight_nodes:
            n_colors.append(highlight_nodes[nd])
        elif node_colors and nd in node_colors:
            n_colors.append(node_colors[nd])
        else:
            n_colors.append("#AEC6CF")


    # edge colours
    edge_list    = list(G.edges())
    e_colors     = []
    e_widths     = []
    hi_set       = set()
    if highlight_edges:
        for e in highlight_edges:
            hi_set.add(e)
            hi_set.add((e[1], e[0]))

    for e in edge_list:
        if e in hi_set:
            e_colors.append(C_ACCENT1)
            e_widths.append(3.0)
        else:
            e_colors.append("#888888")
            e_widths.append(1.0)

    # short labels (first ~14 chars)
    labels = {nd: nd[:14] for nd in G.nodes()}
    edge_labels = {(u, v): str(d["weight"])
                   for u, v, d in G.edges(data=True)}

    nx.draw_networkx_nodes(G, pos, node_color=n_colors,
                           node_size=600, ax=ax)
    nx.draw_networkx_labels(G, pos, labels=labels,
                            font_size=6, ax=ax)
    nx.draw_networkx_edges(G, pos, edge_color=e_colors,
                           width=e_widths, ax=ax,
                           arrows=SHARED.directed,
                           arrowsize=12)
    nx.draw_networkx_edge_labels(G, pos, edge_labels=edge_labels,
                                 font_size=6, ax=ax)

    fig.tight_layout()
    c = FigureCanvasTkAgg(fig, master=canvas_frame)
    c.draw()
    c.get_tk_widget().pack(fill=tk.BOTH, expand=True)
    plt.close(fig)
    return c

# ─────────────────────────────────────────────────────────────────
#  ALGORITHM IMPLEMENTATIONS
# ─────────────────────────────────────────────────────────────────

# ── Welsh-Powell (graph colouring) ──────────────────────────────
def welsh_powell(nodes, edges):
    adj = defaultdict(set)
    for u, v, _ in edges:
        adj[u].add(v)
        adj[v].add(u)
    degree_order = sorted(nodes, key=lambda x: len(adj[x]), reverse=True)
    colour = {}
    c = 0
    for node in degree_order:
        if node not in colour:
            colour[node] = c
            for other in degree_order:
                if other not in colour:
                    if all(colour.get(nb) != c for nb in adj[other]):
                        colour[other] = c
            c += 1
    return colour, c  # returns coloring dict and chromatic number

# ── Kruskal (MST) ───────────────────────────────────────────────
def kruskal(nodes, edges):
    parent = {n: n for n in nodes}
    rank   = {n: 0  for n in nodes}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra == rb:
            return False
        if rank[ra] < rank[rb]:
            ra, rb = rb, ra
        parent[rb] = ra
        if rank[ra] == rank[rb]:
            rank[ra] += 1
        return True

    mst  = []
    cost = 0
    for u, v, w in sorted(edges, key=lambda x: x[2]):
        if union(u, v):
            mst.append((u, v, w))
            cost += w
    return mst, cost

# ── Dijkstra ────────────────────────────────────────────────────
def dijkstra(nodes, edges, source, target=None):
    adj = defaultdict(list)
    for u, v, w in edges:
        adj[u].append((v, w))
        adj[v].append((u, w))   # undirected

    dist = {n: math.inf for n in nodes}
    prev = {n: None     for n in nodes}
    dist[source] = 0
    pq = [(0, source)]

    while pq:
        d, u = heapq.heappop(pq)
        if d > dist[u]:
            continue
        for v, w in adj[u]:
            nd = dist[u] + w
            if nd < dist[v]:
                dist[v] = nd
                prev[v] = u
                heapq.heappush(pq, (nd, v))

    # reconstruct path to target
    path = []
    if target and dist[target] < math.inf:
        cur = target
        while cur is not None:
            path.append(cur)
            cur = prev[cur]
        path.reverse()

    return dist, path

# ── Bellman-Ford ─────────────────────────────────────────────────
def bellman_ford(nodes, edges, source):
    dist = {n: math.inf for n in nodes}
    prev = {n: None     for n in nodes}
    dist[source] = 0

    all_directed = []
    for u, v, w in edges:
        all_directed.append((u, v, w))
        all_directed.append((v, u, w))

    n = len(nodes)
    for _ in range(n - 1):
        for u, v, w in all_directed:
            if dist[u] < math.inf and dist[u] + w < dist[v]:
                dist[v] = dist[u] + w
                prev[v] = u

    neg_cycle = False
    for u, v, w in all_directed:
        if dist[u] < math.inf and dist[u] + w < dist[v]:
            neg_cycle = True
            break

    return dist, prev, neg_cycle

# ── Ford-Fulkerson (BFS / Edmonds-Karp) ─────────────────────────
def ford_fulkerson(nodes, edges, source, sink):
    cap = defaultdict(int)
    for u, v, w in edges:
        cap[(u, v)] += w
        cap[(v, u)] += 0  # reverse

    def bfs(s, t, parent):
        visited = {s}
        queue   = deque([s])
        while queue:
            u = queue.popleft()
            for v in nodes:
                if v not in visited and cap[(u, v)] > 0:
                    visited.add(v)
                    parent[v] = u
                    if v == t:
                        return True
                    queue.append(v)
        return False

    max_flow   = 0
    flow_edges = []
    parent     = {}
    while bfs(source, sink, parent):
        path_flow = math.inf
        s = sink
        while s != source:
            u = parent[s]
            path_flow = min(path_flow, cap[(u, s)])
            s = u
        max_flow += path_flow
        v = sink
        path_taken = []
        while v != source:
            u = parent[v]
            cap[(u, v)] -= path_flow
            cap[(v, u)] += path_flow
            path_taken.append((u, v))
            v = u
        flow_edges.extend(path_taken)
        parent = {}
    return max_flow, flow_edges

# ── Nord-Ouest (North-West Corner) ───────────────────────────────
def nord_ouest(supply, demand):
    s = supply[:]
    d = demand[:]
    m, n = len(s), len(d)
    alloc = [[0]*n for _ in range(m)]
    i = j = 0
    while i < m and j < n:
        a = min(s[i], d[j])
        alloc[i][j] = a
        s[i] -= a
        d[j] -= a
        if s[i] == 0:
            i += 1
        else:
            j += 1
    return alloc

# ── Moindre Coût (Least Cost) ────────────────────────────────────
def moindre_cout(supply, demand, cost):
    s = supply[:]
    d = demand[:]
    m, n = len(s), len(d)
    alloc = [[0]*n for _ in range(m)]

    # Build sorted list of (cost, i, j)
    cells = sorted([(cost[i][j], i, j)
                    for i in range(m) for j in range(n)],
                   key=lambda x: x[0])

    for _, i, j in cells:
        if s[i] > 0 and d[j] > 0:
            a = min(s[i], d[j])
            alloc[i][j] = a
            s[i] -= a
            d[j] -= a
    return alloc

# ── Potentiel-MODI ───────────────────────────────────────────────
def potentiel_modi(supply, demand, cost):
    """MODI method for optimal transportation.
    Returns: optimal allocation, total cost, iteration log."""
    m, n = len(supply), len(demand)
    alloc = moindre_cout(supply[:], demand[:], cost)  # start from LC solution

    log   = []
    max_iter = 50

    for iteration in range(max_iter):
        # find basic cells (non-zero + degenerate set)
        basic = [(i, j) for i in range(m) for j in range(n) if alloc[i][j] > 0]

        # need m+n-1 basic cells
        if len(basic) < m + n - 1:
            # add degenerate cells with epsilon
            for i in range(m):
                for j in range(n):
                    if len(basic) >= m + n - 1:
                        break
                    if (i, j) not in basic:
                        basic.append((i, j))
                if len(basic) >= m + n - 1:
                    break

        # solve dual potentials: u[i] + v[j] = c[i][j] for basic cells
        u = [None]*m
        v = [None]*n
        u[0] = 0
        changed = True
        while changed:
            changed = False
            for (i, j) in basic:
                if u[i] is not None and v[j] is None:
                    v[j] = cost[i][j] - u[i]; changed = True
                elif v[j] is not None and u[i] is None:
                    u[i] = cost[i][j] - v[j]; changed = True

        # fill any remaining None with 0
        u = [x if x is not None else 0 for x in u]
        v = [x if x is not None else 0 for x in v]

        # compute reduced costs
        rc = [[cost[i][j] - u[i] - v[j]
               for j in range(n)] for i in range(m)]

        # find most negative
        min_rc = 0
        enter  = None
        for i in range(m):
            for j in range(n):
                if (i, j) not in basic and rc[i][j] < min_rc:
                    min_rc = rc[i][j]
                    enter  = (i, j)

        if enter is None:
            log.append(f"Iteration {iteration+1}: Optimal solution found.")
            break

        log.append(f"Iteration {iteration+1}: Entering cell {enter}, rc={min_rc:.2f}")

        # find loop (simplified cycle detection using BFS on bipartite graph)
        # For small m,n we use brute-force loop finding
        loop = _find_loop(enter, basic, m, n)
        if not loop:
            log.append("  Could not find loop; stopping.")
            break

        # find min in odd positions (leaving cell)
        odd_vals = [alloc[loop[k][0]][loop[k][1]]
                    for k in range(1, len(loop), 2)]
        theta = min(odd_vals)
        log.append(f"  Theta = {theta}")

        # update allocations
        for k, (i, j) in enumerate(loop):
            if k % 2 == 0:
                alloc[i][j] += theta
            else:
                alloc[i][j] -= theta

    # total cost
    total = sum(alloc[i][j] * cost[i][j]
                for i in range(m) for j in range(n))
    return alloc, total, log

def _find_loop(enter, basic, m, n):
    """Find a closed loop starting from 'enter' using basic cells."""
    basic_set = set(basic)
    basic_set.add(enter)
    rows = defaultdict(list)
    cols = defaultdict(list)
    for (i, j) in basic_set:
        rows[i].append(j)
        cols[j].append(i)

    # DFS to find loop
    def dfs(path, direction):
        cur = path[-1]
        if len(path) >= 4 and cur == enter:
            return path
        i, j = cur
        if direction == 'row':
            for jj in rows[i]:
                nxt = (i, jj)
                if nxt == enter and len(path) >= 4:
                    return path + [enter]
                if nxt not in path:
                    result = dfs(path + [nxt], 'col')
                    if result:
                        return result
        else:
            for ii in cols[j]:
                nxt = (ii, j)
                if nxt == enter and len(path) >= 4:
                    return path + [enter]
                if nxt not in path:
                    result = dfs(path + [nxt], 'row')
                    if result:
                        return result
        return None

    loop = dfs([enter], 'row')
    if loop and loop[-1] == enter:
        return loop[:-1]
    return None

# ── Simplex (user-defined) ────────────────────────────────────────
def simplex_maximize(c, A_ub, b_ub):
    """
    Maximize c·x subject to A_ub·x <= b_ub, x >= 0
    Uses tableau method. Returns (status, x, obj_val, tableau_log).
    """
    m = len(b_ub)
    n = len(c)
    # Add slack variables
    tableau = []
    for i in range(m):
        row = list(A_ub[i]) + [1 if k == i else 0 for k in range(m)] + [b_ub[i]]
        tableau.append(row)
    # Objective row (negate for maximisation)
    obj_row = [-ci for ci in c] + [0]*m + [0]
    tableau.append(obj_row)

    total_vars = n + m
    basis = list(range(n, n + m))  # slack variables are initial basis
    log   = []

    for iteration in range(200):
        obj = tableau[-1]
        # Pivot column: most negative in objective row
        pivot_col = min(range(total_vars), key=lambda j: obj[j])
        if obj[pivot_col] >= -1e-9:
            break  # optimal

        # Pivot row: min ratio test
        ratios = []
        for i in range(m):
            if tableau[i][pivot_col] > 1e-9:
                ratios.append((tableau[i][-1] / tableau[i][pivot_col], i))
        if not ratios:
            return "unbounded", None, None, log

        _, pivot_row = min(ratios)
        basis[pivot_row] = pivot_col
        pv = tableau[pivot_row][pivot_col]

        # Normalise pivot row
        tableau[pivot_row] = [x / pv for x in tableau[pivot_row]]

        # Eliminate pivot column from all other rows
        for i in range(m + 1):
            if i != pivot_row:
                factor = tableau[i][pivot_col]
                tableau[i] = [tableau[i][j] - factor * tableau[pivot_row][j]
                               for j in range(total_vars + 1)]

        obj_val = tableau[-1][-1]
        log.append(f"Iter {iteration+1}: pivot col={pivot_col}, "
                   f"row={pivot_row}, obj={-obj_val:.4f}")

    # Extract solution
    x = [0.0] * total_vars
    for i, b in enumerate(basis):
        x[b] = tableau[i][-1]

    # tableau[-1][-1] holds the negated objective; negate again to get actual max value
    obj_val = tableau[-1][-1]
    return "optimal", x[:n], obj_val, log

# ─────────────────────────────────────────────────────────────────
#  GUI HELPERS
# ─────────────────────────────────────────────────────────────────
def make_button(parent, text, command, bg=C_BTN, fg=C_BTN_TXT,
                width=22, font=FONT_BTN, pady=6):
    b = tk.Button(parent, text=text, command=command,
                  bg=bg, fg=fg, font=font,
                  relief=tk.FLAT, bd=0,
                  activebackground=C_ACCENT1, activeforeground="white",
                  width=width, pady=pady, cursor="hand2")
    return b

def make_label(parent, text, font=FONT_BODY, fg=C_LABEL, bg=C_BG, **kw):
    return tk.Label(parent, text=text, font=font,
                    fg=fg, bg=bg, **kw)

def section_header(parent, text, bg=C_HEADER, fg=C_TITLE_TXT):
    return tk.Label(parent, text=text, font=FONT_SUB,
                    bg=bg, fg=fg, padx=10, pady=6)

def result_box(parent, height=12, width=70):
    frame = tk.Frame(parent, bg=C_BG)
    sb    = tk.Scrollbar(frame)
    txt   = tk.Text(frame, height=height, width=width,
                    bg=C_ENTRY_BG, fg=C_LABEL, font=FONT_MONO,
                    yscrollcommand=sb.set, relief=tk.SUNKEN, bd=1,
                    state=tk.DISABLED)
    sb.config(command=txt.yview)
    sb.pack(side=tk.RIGHT, fill=tk.Y)
    txt.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
    return frame, txt

def write_result(txt_widget, text):
    txt_widget.config(state=tk.NORMAL)
    txt_widget.delete("1.0", tk.END)
    txt_widget.insert(tk.END, text)
    txt_widget.config(state=tk.DISABLED)

def labeled_entry(parent, label_text, default="", width=8, bg=C_BG):
    f   = tk.Frame(parent, bg=bg)
    lbl = tk.Label(f, text=label_text, font=FONT_BODY,
                   fg=C_LABEL, bg=bg)
    lbl.pack(side=tk.LEFT, padx=(0, 4))
    ent = tk.Entry(f, width=width, font=FONT_BODY,
                   bg=C_ENTRY_BG, relief=tk.SOLID, bd=1)
    ent.insert(0, default)
    ent.pack(side=tk.LEFT)
    return f, ent

# ─────────────────────────────────────────────────────────────────
#  GRAPH GENERATOR PANEL  (top of main window)
# ─────────────────────────────────────────────────────────────────
class GraphGeneratorPanel(tk.Frame):
    def __init__(self, parent, on_generate, **kw):
        super().__init__(parent, bg=C_PANEL, relief=tk.GROOVE,
                         bd=2, **kw)
        self.on_generate = on_generate
        self._build()

    def _build(self):
        section_header(self, "  ⚙  Graph Generator",
                       bg=C_HEADER).pack(fill=tk.X)

        row = tk.Frame(self, bg=C_PANEL)
        row.pack(pady=8, padx=12, fill=tk.X)

        # Vertices
        _, self.ent_v = labeled_entry(row, "Vertices (1–100):", "10", 5, C_PANEL)
        _.pack(side=tk.LEFT, padx=8)

        # Density
        _, self.ent_d = labeled_entry(row, "Density % (1–100):", "50", 5, C_PANEL)
        _.pack(side=tk.LEFT, padx=8)

        # Directed
        self.var_dir = tk.BooleanVar(value=False)
        tk.Checkbutton(row, text="Directed", variable=self.var_dir,
                       bg=C_PANEL, fg=C_LABEL, font=FONT_BODY,
                       activebackground=C_PANEL,
                       selectcolor=C_ENTRY_BG).pack(side=tk.LEFT, padx=8)

        # Seed
        _, self.ent_seed = labeled_entry(row, "Seed (opt):", "", 5, C_PANEL)
        _.pack(side=tk.LEFT, padx=8)

        make_button(row, "🔄  Generate Graph",
                    self._generate, width=18).pack(side=tk.LEFT, padx=12)

        # ── Algorithm selector ────────────────────────────────────
        algo_row = tk.Frame(self, bg=C_PANEL)
        algo_row.pack(pady=(0, 8), padx=12, fill=tk.X)

        tk.Label(algo_row, text="Algorithm to run:",
                 font=FONT_BODY, fg=C_LABEL, bg=C_PANEL).pack(side=tk.LEFT, padx=(0, 6))

        self.cmb_algo = ttk.Combobox(algo_row, state="readonly",
                                     font=FONT_BODY, width=28,
                                     values=self._algo_labels())
        self.cmb_algo.current(1)
        self.cmb_algo.pack(side=tk.LEFT, padx=(0, 8))

        make_button(algo_row, "▶  Run Algorithm", self._run_algo,
                    bg=C_ACCENT2, width=16).pack(side=tk.LEFT, padx=4)

        self.var_auto = tk.BooleanVar(value=True)
        tk.Checkbutton(algo_row, text="Auto-open after Generate",
                       variable=self.var_auto,
                       bg=C_PANEL, fg=C_LABEL, font=FONT_BODY,
                       activebackground=C_PANEL,
                       selectcolor=C_ENTRY_BG).pack(side=tk.LEFT, padx=8)

        # Status label
        self.lbl_status = tk.Label(self, text="No graph generated yet.",
                                   font=FONT_SMALL, fg=C_ACCENT3,
                                   bg=C_PANEL)
        self.lbl_status.pack(pady=(0, 6))

    def _generate(self):
        try:
            n = int(self.ent_v.get())
            d = int(self.ent_d.get())
        except ValueError:
            messagebox.showerror("Input Error",
                                 "Please enter valid integers for vertices and density.")
            return
        if not (1 <= n <= 100):
            messagebox.showerror("Range Error", "Vertices must be between 1 and 100.")
            return
        if not (1 <= d <= 100):
            messagebox.showerror("Range Error", "Density must be between 1 and 100.")
            return

        seed_str = self.ent_seed.get().strip()
        seed = int(seed_str) if seed_str.isdigit() else None
        SHARED.generate(n, d, self.var_dir.get(), seed)
        self.lbl_status.config(
            text=f"✔  Graph generated: {n} vertices, "
                 f"{len(SHARED.edges)} edges, "
                 f"{'directed' if SHARED.directed else 'undirected'}.",
            fg=C_ACCENT2)
        self.on_generate()

        # Optionally jump straight into the selected algorithm
        if self.var_auto.get():
            factory = self._algo_factory(self.cmb_algo.get())
            if factory:
                factory(self.master)

    def _algo_labels(self):
        return [
            "— Select Algorithm —",
            "Welsh-Powell — Graph Colouring",
            "Kruskal — Min Spanning Tree",
            "Dijkstra — Shortest Path",
            "Bellman-Ford — Shortest Paths",
            "Ford-Fulkerson — Max Flow",
            "Nord-Ouest — Transport",
            "Moindre Coût — Transport",
            "Potentiel-MODI — Transport",
            "Simplex — Linear Programming",
        ]

    def _algo_factory(self, choice):
        mapping = {
            "Welsh-Powell — Graph Colouring": lambda p: WelshPowellWindow(p),
            "Kruskal — Min Spanning Tree":    lambda p: KruskalWindow(p),
            "Dijkstra — Shortest Path":       lambda p: DijkstraWindow(p),
            "Bellman-Ford — Shortest Paths":  lambda p: BellmanFordWindow(p),
            "Ford-Fulkerson — Max Flow":      lambda p: FordFulkersonWindow(p),
            "Nord-Ouest — Transport":         lambda p: TransportWindow(p, "nord_ouest"),
            "Moindre Coût — Transport":       lambda p: TransportWindow(p, "moindre_cout"),
            "Potentiel-MODI — Transport":     lambda p: TransportWindow(p, "potentiel"),
            "Simplex — Linear Programming":   lambda p: SimplexWindow(p),
        }
        return mapping.get(choice)

    def _run_algo(self):
        if not SHARED.generated:
            messagebox.showwarning("No Graph", "Generate a graph first.")
            return
        factory = self._algo_factory(self.cmb_algo.get())
        if factory is None:
            messagebox.showinfo("Select Algorithm",
                                 "Choose an algorithm from the dropdown first.")
            return
        factory(self.master)

# ─────────────────────────────────────────────────────────────────
#  BASE ALGORITHM WINDOW
# ─────────────────────────────────────────────────────────────────
class AlgoWindow(tk.Toplevel):
    def __init__(self, parent, title, width=1100, height=720):
        super().__init__(parent)
        self.title(f"EMI — {title}")
        self.geometry(f"{width}x{height}")
        self.configure(bg=C_BG)
        self.resizable(True, True)

        # header
        hdr = tk.Frame(self, bg=C_HEADER, pady=6)
        hdr.pack(fill=tk.X)
        tk.Label(hdr, text=f"  {title}",
                 font=FONT_TITLE, fg=C_TITLE_TXT,
                 bg=C_HEADER).pack(side=tk.LEFT)
        tk.Label(hdr, text="Ecole Mohammadia d'Ingénieurs — Fadlaoui Abd-essamade",
                 font=FONT_SMALL, fg="#AAAAAA",
                 bg=C_HEADER).pack(side=tk.RIGHT, padx=12)

        # main paned
        self.paned = tk.PanedWindow(self, orient=tk.HORIZONTAL,
                                    bg=C_BG, sashwidth=6,
                                    sashrelief=tk.RIDGE)
        self.paned.pack(fill=tk.BOTH, expand=True, padx=4, pady=4)

        # left panel (controls + results)
        self.left = tk.Frame(self.paned, bg=C_BG, width=380)
        self.paned.add(self.left, minsize=300)

        # right panel (graph)
        self.graph_frame = tk.Frame(self.paned, bg=C_BG)
        self.paned.add(self.graph_frame, minsize=400)

        self._build_controls()
        self._draw_graph()  # show existing shared graph immediately

    def _build_controls(self):
        """Override in subclass."""
        pass

    def _draw_graph(self, **kw):
        draw_graph_on_canvas(self.graph_frame, **kw)

# ─────────────────────────────────────────────────────────────────
#  WELSH-POWELL WINDOW
# ─────────────────────────────────────────────────────────────────
class WelshPowellWindow(AlgoWindow):
    def __init__(self, parent):
        super().__init__(parent, "Welsh-Powell — Graph Colouring")

    def _build_controls(self):
        section_header(self.left,
                       "Welsh-Powell Algorithm",
                       bg=C_ACCENT1).pack(fill=tk.X, pady=(0, 8))

        info = (
            "The Welsh-Powell algorithm colours a graph such that\n"
            "no two adjacent nodes share the same colour.\n\n"
            "Application: Frequency assignment in Moroccan\n"
            "telecom/power networks to avoid interference.\n\n"
            "Reference Project: Casablanca Smart Grid Pilot\n"
            "— Channel allocation for smart meters."
        )
        tk.Label(self.left, text=info, font=FONT_SMALL,
                 bg=C_BG, fg=C_LABEL, justify=tk.LEFT,
                 wraplength=360).pack(padx=10, pady=4)

        make_button(self.left, "▶  Run Welsh-Powell",
                    self._run).pack(pady=10)

        rf, self.result_txt = result_box(self.left, height=14)
        rf.pack(fill=tk.BOTH, expand=True, padx=8, pady=4)

    def _run(self):
        if not SHARED.generated:
            messagebox.showwarning("No Graph", "Generate a graph first.")
            return

        colour_map, chromatic = welsh_powell(SHARED.nodes, SHARED.edges)
        # Assign distinct colours for visualisation
        palette = [
            "#E74C3C","#27AE60","#F39C12","#8E44AD",
            "#1ABC9C","#2980B9","#E67E22","#C0392B",
            "#16A085","#D35400","#7F8C8D","#2C3E50"
        ]
        node_colors = {n: palette[c % len(palette)]
                       for n, c in colour_map.items()}

        self._draw_graph(highlight_nodes=node_colors,
                         title=f"Welsh-Powell Colouring (χ = {chromatic})")

        lines = [f"Welsh-Powell Graph Colouring\n{'='*40}",
                 f"Chromatic Number χ = {chromatic}\n"]
        # group by colour
        by_color = defaultdict(list)
        for nd, c in colour_map.items():
            by_color[c].append(nd)
        for c in sorted(by_color):
            lines.append(f"Colour {c+1}:  {', '.join(by_color[c])}")

        lines += ["",
                  "Engineering Context:",
                  f"  Project : Casablanca Smart Grid Pilot",
                  f"  Task    : Frequency assignment for {len(SHARED.nodes)} substations",
                  f"  Result  : Only {chromatic} distinct frequencies needed."]
        write_result(self.result_txt, "\n".join(lines))

# ─────────────────────────────────────────────────────────────────
#  KRUSKAL WINDOW
# ─────────────────────────────────────────────────────────────────
class KruskalWindow(AlgoWindow):
    def __init__(self, parent):
        super().__init__(parent, "Kruskal — Minimum Spanning Tree")

    def _build_controls(self):
        section_header(self.left, "Kruskal Algorithm",
                       bg=C_ACCENT1).pack(fill=tk.X, pady=(0, 8))

        info = (
            "Kruskal finds the Minimum Spanning Tree (MST)\n"
            "of a weighted graph — the cheapest set of edges\n"
            "that connects all nodes.\n\n"
            "Application: Optimal transmission line planning\n"
            "across Moroccan cities to minimise cable length.\n\n"
            "Reference Project: ONEE 400 kV Backbone —\n"
            "Minimum-cost grid linking all major substations."
        )
        tk.Label(self.left, text=info, font=FONT_SMALL,
                 bg=C_BG, fg=C_LABEL, justify=tk.LEFT,
                 wraplength=360).pack(padx=10, pady=4)

        make_button(self.left, "▶  Run Kruskal",
                    self._run).pack(pady=10)

        rf, self.result_txt = result_box(self.left, height=14)
        rf.pack(fill=tk.BOTH, expand=True, padx=8, pady=4)

    def _run(self):
        if not SHARED.generated:
            messagebox.showwarning("No Graph", "Generate a graph first.")
            return

        mst, total_cost = kruskal(SHARED.nodes, SHARED.edges)
        hi_edges = [(u, v) for u, v, _ in mst]
        self._draw_graph(highlight_edges=hi_edges,
                         title=f"Kruskal MST  (Total Weight = {total_cost})")

        lines = [f"Kruskal Minimum Spanning Tree\n{'='*40}",
                 f"Total MST Weight : {total_cost} km (or MW-equivalent)",
                 f"MST Edges        : {len(mst)} / {len(SHARED.edges)}",
                 ""]
        for i, (u, v, w) in enumerate(mst, 1):
            lines.append(f"  {i:2d}. {u[:20]} — {v[:20]}   weight={w}")

        lines += ["",
                  "Engineering Context:",
                  "  Project : ONEE 400 kV Backbone",
                  f"  Nodes   : {len(SHARED.nodes)} substations",
                  f"  Saving  : Connects all nodes with minimum total cable."]
        write_result(self.result_txt, "\n".join(lines))

# ─────────────────────────────────────────────────────────────────
#  DIJKSTRA WINDOW
# ─────────────────────────────────────────────────────────────────
class DijkstraWindow(AlgoWindow):
    def __init__(self, parent):
        super().__init__(parent, "Dijkstra — Shortest Path")

    def _build_controls(self):
        section_header(self.left, "Dijkstra Algorithm",
                       bg=C_ACCENT1).pack(fill=tk.X, pady=(0, 8))

        info = (
            "Dijkstra computes the shortest path between two\n"
            "nodes in a non-negative weighted graph.\n\n"
            "Application: Minimum energy routing between\n"
            "Moroccan power stations / substations.\n\n"
            "Reference Project: Noor Ouarzazate — optimal\n"
            "dispatch path to national grid."
        )
        tk.Label(self.left, text=info, font=FONT_SMALL,
                 bg=C_BG, fg=C_LABEL, justify=tk.LEFT,
                 wraplength=360).pack(padx=10, pady=4)

        # Source selection
        src_frame = tk.Frame(self.left, bg=C_BG)
        src_frame.pack(fill=tk.X, padx=10, pady=4)
        tk.Label(src_frame, text="Source Station:",
                 font=FONT_BODY, bg=C_BG, fg=C_LABEL).pack(anchor=tk.W)
        self.cmb_src = ttk.Combobox(src_frame, state="readonly",
                                     font=FONT_BODY)
        self.cmb_src.pack(fill=tk.X, pady=2)

        # Target selection
        tgt_frame = tk.Frame(self.left, bg=C_BG)
        tgt_frame.pack(fill=tk.X, padx=10, pady=4)
        tk.Label(tgt_frame, text="Destination Station:",
                 font=FONT_BODY, bg=C_BG, fg=C_LABEL).pack(anchor=tk.W)
        self.cmb_tgt = ttk.Combobox(tgt_frame, state="readonly",
                                     font=FONT_BODY)
        self.cmb_tgt.pack(fill=tk.X, pady=2)

        self._refresh_combos()

        make_button(self.left, "▶  Run Dijkstra",
                    self._run).pack(pady=10)

        # Refresh combo when graph changes
        make_button(self.left, "↻  Refresh Station List",
                    self._refresh_combos,
                    bg=C_ACCENT2, width=22).pack(pady=2)

        rf, self.result_txt = result_box(self.left, height=12)
        rf.pack(fill=tk.BOTH, expand=True, padx=8, pady=4)

    def _refresh_combos(self):
        nodes = SHARED.nodes if SHARED.generated else []
        self.cmb_src["values"] = nodes
        self.cmb_tgt["values"] = nodes
        if nodes:
            self.cmb_src.set(nodes[0])
            self.cmb_tgt.set(nodes[-1])

    def _run(self):
        if not SHARED.generated:
            messagebox.showwarning("No Graph", "Generate a graph first.")
            return

        source = self.cmb_src.get()
        target = self.cmb_tgt.get()

        if not source or not target:
            messagebox.showerror("Selection Error",
                                 "Please select both source and destination.")
            return
        if source == target:
            messagebox.showerror("Selection Error",
                                 "Source and destination must differ.")
            return
        if source not in SHARED.nodes or target not in SHARED.nodes:
            messagebox.showerror("Selection Error",
                                 "Selected stations not in current graph. "
                                 "Click 'Refresh Station List'.")
            return

        dist, path = dijkstra(SHARED.nodes, SHARED.edges, source, target)

        hi_edges = [(path[i], path[i+1]) for i in range(len(path)-1)]
        nc = {source: "#F1C40F",  # gold = source
              target: "#27AE60"}  # green = destination
        for nd in path[1:-1]:
            nc[nd] = "#E74C3C"    # red = path nodes

        self._draw_graph(highlight_edges=hi_edges,
                         highlight_nodes=nc,
                         title=f"Dijkstra: {source[:16]} → {target[:16]}")

        lines = [f"Dijkstra Shortest Path\n{'='*40}",
                 f"Source      : {source}",
                 f"Destination : {target}",
                 f"Distance    : {dist[target] if dist[target] < math.inf else 'Unreachable'}",
                 ""]

        if path:
            lines.append("Path:")
            for i, nd in enumerate(path):
                arrow = " →" if i < len(path)-1 else ""
                lines.append(f"  {i+1}. {nd}{arrow}")
        else:
            lines.append("  No path found between these stations.")

        lines += ["",
                  "All Shortest Distances from Source:",
                  "─"*38]
        for nd in sorted(SHARED.nodes):
            d = dist[nd]
            dstr = str(d) if d < math.inf else "∞ (unreachable)"
            lines.append(f"  {nd[:30]:<30} : {dstr}")

        write_result(self.result_txt, "\n".join(lines))

# ─────────────────────────────────────────────────────────────────
#  BELLMAN-FORD WINDOW
# ─────────────────────────────────────────────────────────────────
class BellmanFordWindow(AlgoWindow):
    def __init__(self, parent):
        super().__init__(parent, "Bellman-Ford — Shortest Paths")

    def _build_controls(self):
        section_header(self.left, "Bellman-Ford Algorithm",
                       bg=C_ACCENT1).pack(fill=tk.X, pady=(0, 8))

        info = (
            "Bellman-Ford computes shortest paths from a single\n"
            "source and detects negative-weight cycles.\n\n"
            "Application: Fault current analysis in power\n"
            "networks (negative weights = energy recovery).\n\n"
            "Reference Project: Jorf Lasfar Power Plant —\n"
            "optimal power distribution to industrial clients."
        )
        tk.Label(self.left, text=info, font=FONT_SMALL,
                 bg=C_BG, fg=C_LABEL, justify=tk.LEFT,
                 wraplength=360).pack(padx=10, pady=4)

        src_frame = tk.Frame(self.left, bg=C_BG)
        src_frame.pack(fill=tk.X, padx=10, pady=4)
        tk.Label(src_frame, text="Source Station:",
                 font=FONT_BODY, bg=C_BG, fg=C_LABEL).pack(anchor=tk.W)
        self.cmb_src = ttk.Combobox(src_frame, state="readonly",
                                     font=FONT_BODY)
        self.cmb_src.pack(fill=tk.X, pady=2)
        self._refresh_combo()

        make_button(self.left, "▶  Run Bellman-Ford",
                    self._run).pack(pady=10)
        make_button(self.left, "↻  Refresh Station List",
                    self._refresh_combo,
                    bg=C_ACCENT2, width=22).pack(pady=2)

        rf, self.result_txt = result_box(self.left, height=14)
        rf.pack(fill=tk.BOTH, expand=True, padx=8, pady=4)

    def _refresh_combo(self):
        nodes = SHARED.nodes if SHARED.generated else []
        self.cmb_src["values"] = nodes
        if nodes:
            self.cmb_src.set(nodes[0])

    def _run(self):
        if not SHARED.generated:
            messagebox.showwarning("No Graph", "Generate a graph first.")
            return

        source = self.cmb_src.get()
        if not source or source not in SHARED.nodes:
            messagebox.showerror("Error", "Select a valid source station.")
            return

        dist, prev, neg_cycle = bellman_ford(SHARED.nodes, SHARED.edges, source)

        nc = {source: "#F1C40F"}
        # colour nodes by distance buckets
        finite = [d for d in dist.values() if d < math.inf]
        if finite:
            mx = max(finite) or 1
            for nd, d in dist.items():
                if nd == source:
                    continue
                if d == math.inf:
                    nc[nd] = "#BDC3C7"
                else:
                    ratio = d / mx
                    r = int(231 * ratio)
                    g = int(76  * (1-ratio))
                    b = 60
                    nc[nd] = f"#{r:02x}{g:02x}{b:02x}"

        self._draw_graph(highlight_nodes=nc,
                         title=f"Bellman-Ford from {source[:18]}")

        lines = [f"Bellman-Ford Shortest Paths\n{'='*40}",
                 f"Source : {source}",
                 f"Negative Cycle : {'YES ⚠' if neg_cycle else 'None detected'}",
                 ""]

        lines.append(f"{'Station':<32} {'Distance':>12}")
        lines.append("─"*46)
        for nd in sorted(SHARED.nodes):
            d = dist[nd]
            dstr = str(d) if d < math.inf else "∞"
            lines.append(f"  {nd[:30]:<30} {dstr:>12}")

        lines += ["",
                  "Engineering Context:",
                  "  Project : Jorf Lasfar Industrial Supply",
                  "  Edges represent MW·km transmission cost."]
        write_result(self.result_txt, "\n".join(lines))

# ─────────────────────────────────────────────────────────────────
#  FORD-FULKERSON WINDOW
# ─────────────────────────────────────────────────────────────────
class FordFulkersonWindow(AlgoWindow):
    def __init__(self, parent):
        super().__init__(parent, "Ford-Fulkerson — Maximum Flow")

    def _build_controls(self):
        section_header(self.left, "Ford-Fulkerson Algorithm",
                       bg=C_ACCENT1).pack(fill=tk.X, pady=(0, 8))

        info = (
            "Ford-Fulkerson computes the maximum flow through\n"
            "a network from a source to a sink.\n\n"
            "Application: Maximum power transmission capacity\n"
            "between generation and consumption centres in Morocco.\n\n"
            "Reference Project: Wind Farm Tarfaya — max MW\n"
            "deliverable to Casablanca via existing grid."
        )
        tk.Label(self.left, text=info, font=FONT_SMALL,
                 bg=C_BG, fg=C_LABEL, justify=tk.LEFT,
                 wraplength=360).pack(padx=10, pady=4)

        src_frame = tk.Frame(self.left, bg=C_BG)
        src_frame.pack(fill=tk.X, padx=10, pady=4)
        tk.Label(src_frame, text="Source (Generation):",
                 font=FONT_BODY, bg=C_BG, fg=C_LABEL).pack(anchor=tk.W)
        self.cmb_src = ttk.Combobox(src_frame, state="readonly", font=FONT_BODY)
        self.cmb_src.pack(fill=tk.X, pady=2)

        tgt_frame = tk.Frame(self.left, bg=C_BG)
        tgt_frame.pack(fill=tk.X, padx=10, pady=4)
        tk.Label(tgt_frame, text="Sink (Consumption):",
                 font=FONT_BODY, bg=C_BG, fg=C_LABEL).pack(anchor=tk.W)
        self.cmb_tgt = ttk.Combobox(tgt_frame, state="readonly", font=FONT_BODY)
        self.cmb_tgt.pack(fill=tk.X, pady=2)

        self._refresh_combos()

        make_button(self.left, "▶  Run Ford-Fulkerson",
                    self._run).pack(pady=10)
        make_button(self.left, "↻  Refresh Station List",
                    self._refresh_combos, bg=C_ACCENT2, width=22).pack(pady=2)

        rf, self.result_txt = result_box(self.left, height=12)
        rf.pack(fill=tk.BOTH, expand=True, padx=8, pady=4)

    def _refresh_combos(self):
        nodes = SHARED.nodes if SHARED.generated else []
        self.cmb_src["values"] = nodes
        self.cmb_tgt["values"] = nodes
        if nodes:
            self.cmb_src.set(nodes[0])
            self.cmb_tgt.set(nodes[-1])

    def _run(self):
        if not SHARED.generated:
            messagebox.showwarning("No Graph", "Generate a graph first.")
            return

        source = self.cmb_src.get()
        sink   = self.cmb_tgt.get()
        if source == sink:
            messagebox.showerror("Error", "Source and sink must differ.")
            return
        if source not in SHARED.nodes or sink not in SHARED.nodes:
            messagebox.showerror("Error", "Invalid selection. Refresh list.")
            return

        max_flow, flow_edges = ford_fulkerson(
            SHARED.nodes, SHARED.edges, source, sink)

        hi = list(set(flow_edges))
        nc = {source: "#F1C40F", sink: "#E74C3C"}
        self._draw_graph(highlight_edges=hi, highlight_nodes=nc,
                         title=f"Ford-Fulkerson Max Flow = {max_flow} MW")

        lines = [f"Ford-Fulkerson Maximum Flow\n{'='*40}",
                 f"Source (Generation) : {source}",
                 f"Sink   (Consumption): {sink}",
                 f"Maximum Flow        : {max_flow} MW",
                 "",
                 "Saturated / Used Edges:"]
        for u, v in set(flow_edges):
            lines.append(f"  {u[:22]} → {v[:22]}")

        lines += ["",
                  "Engineering Context:",
                  "  Project : Wind Farm Tarfaya",
                  "  Unit    : Edge weights represent MW capacity."]
        write_result(self.result_txt, "\n".join(lines))

# ─────────────────────────────────────────────────────────────────
#  TRANSPORT WINDOW (Nord-Ouest, Moindre Coût, Potentiel-MODI)
# ─────────────────────────────────────────────────────────────────
class TransportWindow(tk.Toplevel):
    def __init__(self, parent, method="nord_ouest"):
        super().__init__(parent)
        self.method = method
        titles = {
            "nord_ouest"   : "Nord-Ouest — Transportation Method",
            "moindre_cout" : "Moindre Coût — Least Cost Method",
            "potentiel"    : "Potentiel-MODI — Optimal Transport"
        }
        self.title(f"EMI — {titles.get(method, method)}")
        self.geometry("1050x720")
        self.configure(bg=C_BG)
        self.resizable(True, True)

        # header
        hdr = tk.Frame(self, bg=C_HEADER, pady=6)
        hdr.pack(fill=tk.X)
        tk.Label(hdr, text=f"  {titles.get(method, method)}",
                 font=FONT_TITLE, fg=C_TITLE_TXT,
                 bg=C_HEADER).pack(side=tk.LEFT)
        tk.Label(hdr, text="EMI — Fadlaoui Abd-essamade",
                 font=FONT_SMALL, fg="#AAAAAA",
                 bg=C_HEADER).pack(side=tk.RIGHT, padx=12)

        # main layout
        self.paned = tk.PanedWindow(self, orient=tk.HORIZONTAL,
                                    bg=C_BG, sashwidth=6)
        self.paned.pack(fill=tk.BOTH, expand=True, padx=4, pady=4)

        self.left = tk.Frame(self.paned, bg=C_BG, width=440)
        self.paned.add(self.left, minsize=380)

        self.right = tk.Frame(self.paned, bg=C_BG)
        self.paned.add(self.right, minsize=400)

        self.m_var = tk.StringVar(value="3")
        self.n_var = tk.StringVar(value="4")
        self._build_size_panel()
        self._build_table()

    def _build_size_panel(self):
        top = tk.Frame(self.left, bg=C_PANEL, relief=tk.GROOVE, bd=2)
        top.pack(fill=tk.X, padx=6, pady=4)
        section_header(top, "  Transportation Problem Setup",
                        bg=C_ACCENT3).pack(fill=tk.X)

        row = tk.Frame(top, bg=C_PANEL)
        row.pack(pady=6, padx=8)

        tk.Label(row, text="Suppliers (m):",
                 font=FONT_BODY, bg=C_PANEL, fg=C_LABEL).pack(side=tk.LEFT)
        self.ent_m = tk.Entry(row, textvariable=self.m_var, width=4,
                              font=FONT_BODY, bg=C_ENTRY_BG)
        self.ent_m.pack(side=tk.LEFT, padx=6)

        tk.Label(row, text="Consumers (n):",
                 font=FONT_BODY, bg=C_PANEL, fg=C_LABEL).pack(side=tk.LEFT, padx=(12,0))
        self.ent_n = tk.Entry(row, textvariable=self.n_var, width=4,
                              font=FONT_BODY, bg=C_ENTRY_BG)
        self.ent_n.pack(side=tk.LEFT, padx=6)

        make_button(row, "Build Table", self._build_table,
                    width=12).pack(side=tk.LEFT, padx=8)

        info = {
            "nord_ouest"  : "North-West Corner: fills from top-left corner.",
            "moindre_cout": "Least Cost: fills cheapest cell first.",
            "potentiel"   : "Potentiel-MODI: iterates to optimal solution.",
        }
        tk.Label(top, text=info.get(self.method, ""),
                 font=FONT_SMALL, bg=C_PANEL, fg=C_LABEL,
                 wraplength=400).pack(padx=8, pady=(2,6))

        # Moroccan context
        ctx = (
            "Moroccan Context: Distribution of electrical energy from\n"
            "production sites (Noor Solar, Tarfaya Wind, Jorf Lasfar)\n"
            "to consumption regions (Grand Casablanca, Souss, Oriental…)."
        )
        tk.Label(top, text=ctx, font=FONT_SMALL, bg=C_PANEL, fg=C_ACCENT3,
                 justify=tk.LEFT).pack(padx=8, pady=(0,4))

    def _build_table(self):
        try:
            m = int(self.m_var.get())
            n = int(self.n_var.get())
        except ValueError:
            messagebox.showerror("Error", "Enter valid integers for m and n.")
            return
        if not (1 <= m <= 8 and 1 <= n <= 8):
            messagebox.showerror("Error", "m and n must be between 1 and 8.")
            return

        self.m_val = m
        self.n_val = n

        # clear old table frame
        if hasattr(self, "table_frame"):
            self.table_frame.destroy()

        suppliers = [f"S{i+1}-{PROJECTS[i % len(PROJECTS)][:10]}"
                     for i in range(m)]
        consumers = [f"D{j+1}-{MOROCCAN_CITIES[j % len(MOROCCAN_CITIES)][:8]}"
                     for j in range(n)]

        self.table_frame = tk.Frame(self.left, bg=C_BG)
        self.table_frame.pack(fill=tk.BOTH, expand=True, padx=6, pady=4)

        section_header(self.table_frame,
                       "  Enter Cost Matrix, Supply & Demand",
                       bg=C_HEADER).pack(fill=tk.X, pady=(0,4))

        grid_frame = tk.Frame(self.table_frame, bg=C_BG)
        grid_frame.pack(padx=6)

        # Column headers
        tk.Label(grid_frame, text="", width=8,
                 bg=C_BG).grid(row=0, column=0)
        for j, cname in enumerate(consumers):
            tk.Label(grid_frame, text=cname, font=FONT_SMALL,
                     bg=C_PANEL, fg=C_LABEL,
                     relief=tk.GROOVE, bd=1,
                     width=8, wraplength=70).grid(row=0, column=j+1, padx=1, pady=1)
        tk.Label(grid_frame, text="Supply", font=FONT_SMALL,
                 bg=C_ACCENT2, fg="white",
                 width=8).grid(row=0, column=n+1, padx=1)

        # Cost entries
        self.cost_entries  = []
        self.supply_entries = []

        for i, sname in enumerate(suppliers):
            tk.Label(grid_frame, text=sname, font=FONT_SMALL,
                     bg=C_PANEL, fg=C_LABEL,
                     relief=tk.GROOVE, bd=1,
                     width=8, wraplength=70).grid(row=i+1, column=0, padx=1, pady=1)
            row_entries = []
            for j in range(n):
                e = tk.Entry(grid_frame, width=7, font=FONT_MONO,
                             bg=C_ENTRY_BG, justify=tk.CENTER)
                # random cost
                e.insert(0, str(random.randint(5, 80)))
                e.grid(row=i+1, column=j+1, padx=1, pady=1)
                row_entries.append(e)
            self.cost_entries.append(row_entries)

            se = tk.Entry(grid_frame, width=7, font=FONT_MONO,
                          bg="#D5F5E3", justify=tk.CENTER)
            se.insert(0, str(random.randint(50, 300)))
            se.grid(row=i+1, column=n+1, padx=1, pady=1)
            self.supply_entries.append(se)

        # Demand row
        tk.Label(grid_frame, text="Demand", font=FONT_SMALL,
                 bg=C_ACCENT1, fg="white",
                 width=8).grid(row=m+1, column=0, padx=1)
        self.demand_entries = []
        for j in range(n):
            de = tk.Entry(grid_frame, width=7, font=FONT_MONO,
                          bg="#FAD7A0", justify=tk.CENTER)
            de.insert(0, str(random.randint(40, 250)))
            de.grid(row=m+1, column=j+1, padx=1, pady=1)
            self.demand_entries.append(de)

        # run button
        run_frame = tk.Frame(self.table_frame, bg=C_BG)
        run_frame.pack(pady=6)
        make_button(run_frame, "▶  Randomise Values",
                    self._randomise, bg=C_ACCENT3, width=18).pack(side=tk.LEFT, padx=4)
        make_button(run_frame, "▶  Run Algorithm",
                    self._run, width=16).pack(side=tk.LEFT, padx=4)

        # results
        rf, self.result_txt = result_box(self.table_frame, height=10, width=60)
        rf.pack(fill=tk.BOTH, expand=True, padx=4, pady=2)

    def _randomise(self):
        m, n = self.m_val, self.n_val
        total_supply = 0
        total_demand = 0
        for i in range(m):
            v = random.randint(50, 300)
            total_supply += v
            self.supply_entries[i].delete(0, tk.END)
            self.supply_entries[i].insert(0, str(v))
            for j in range(n):
                self.cost_entries[i][j].delete(0, tk.END)
                self.cost_entries[i][j].insert(0, str(random.randint(5, 80)))
        for j in range(n):
            v = random.randint(40, 250)
            total_demand += v
            self.demand_entries[j].delete(0, tk.END)
            self.demand_entries[j].insert(0, str(v))
        # balance supply = demand (adjust last supply)
        diff = total_demand - total_supply
        cur = int(self.supply_entries[-1].get())
        new_val = max(1, cur + diff)
        self.supply_entries[-1].delete(0, tk.END)
        self.supply_entries[-1].insert(0, str(new_val))

    def _run(self):
        m, n = self.m_val, self.n_val
        try:
            supply = [int(self.supply_entries[i].get()) for i in range(m)]
            demand = [int(self.demand_entries[j].get()) for j in range(n)]
            cost   = [[int(self.cost_entries[i][j].get())
                       for j in range(n)] for i in range(m)]
        except ValueError:
            messagebox.showerror("Input Error",
                                 "All cells must contain integers.")
            return

        # Balance check
        ts, td = sum(supply), sum(demand)
        if ts != td:
            # Auto-balance with dummy row or column
            if ts > td:
                demand.append(ts - td)
                for i in range(m):
                    cost[i].append(0)
                n += 1
                messagebox.showinfo(
                    "Balancing",
                    f"Unbalanced problem (supply={ts}, demand={td}).\n"
                    f"Added dummy destination with demand={ts-td}.")
            else:
                supply.append(td - ts)
                cost.append([0]*n)
                m += 1
                messagebox.showinfo(
                    "Balancing",
                    f"Unbalanced problem (supply={ts}, demand={td}).\n"
                    f"Added dummy source with supply={td-ts}.")

        if self.method == "nord_ouest":
            alloc = nord_ouest(supply[:], demand[:])
            log   = ["Nord-Ouest (North-West Corner) Method"]
            total = sum(alloc[i][j]*cost[i][j]
                        for i in range(len(supply))
                        for j in range(len(demand)))
        elif self.method == "moindre_cout":
            alloc = moindre_cout(supply[:], demand[:], cost)
            log   = ["Moindre Coût (Least Cost) Method"]
            total = sum(alloc[i][j]*cost[i][j]
                        for i in range(len(supply))
                        for j in range(len(demand)))
        else:  # potentiel
            alloc, total, log = potentiel_modi(supply[:], demand[:], cost)

        # Draw transport matrix as a heatmap
        self._draw_transport(alloc, cost, supply, demand)

        # text result
        header_line = "=" * 44
        lines = [log[0] if log else "Transportation Result",
                 header_line,
                 f"Total Transportation Cost : {total}",
                 ""]
        if self.method == "potentiel" and len(log) > 1:
            lines.append("MODI Iterations:")
            lines.extend(log[1:])
            lines.append("")

        lines.append("Allocation Matrix:")
        lines.append(f"{'':10}" + "".join(
            f"D{j+1:>5}" for j in range(len(demand))))
        for i in range(len(supply)):
            row_str = f"S{i+1:<8}" + "".join(
                f"{alloc[i][j]:>6}" for j in range(len(demand)))
            lines.append(row_str)

        write_result(self.result_txt, "\n".join(lines))

    def _draw_transport(self, alloc, cost, supply, demand):
        for w in self.right.winfo_children():
            w.destroy()

        if not HAS_PLOT:
            return

        m = len(supply)
        n = len(demand)
        fig, ax = plt.subplots(figsize=(7, 5), facecolor=C_BG)
        ax.set_facecolor(C_BG)
        ax.set_title(f"Allocation Matrix — {self.title()}",
                     fontsize=10, fontweight="bold", color=C_HEADER)

        # draw cells
        for i in range(m):
            for j in range(n):
                a = alloc[i][j]
                c = cost[i][j]
                # shade by allocation
                alpha = min(0.9, a / max(1, max(supply)))
                rect = plt.Rectangle([j, m-1-i], 1, 1,
                                     facecolor=f"#{'%02x'%int(46+200*(1-alpha))}"
                                               f"{'%02x'%int(134+50*alpha)}"
                                               f"{'%02x'%int(193-150*alpha)}",
                                     edgecolor="#888888", linewidth=0.8)
                ax.add_patch(rect)
                ax.text(j+0.5, m-1-i+0.7, f"c={c}",
                        ha="center", va="center",
                        fontsize=7, color="#333333")
                ax.text(j+0.5, m-1-i+0.3, f"x={a}",
                        ha="center", va="center",
                        fontsize=8, fontweight="bold",
                        color=C_ACCENT1 if a > 0 else "#AAAAAA")

        ax.set_xlim(0, n)
        ax.set_ylim(0, m)
        ax.set_xticks([j+0.5 for j in range(n)])
        ax.set_xticklabels([f"D{j+1}\n({demand[j]})" for j in range(n)],
                           fontsize=8)
        ax.set_yticks([i+0.5 for i in range(m)])
        ax.set_yticklabels([f"S{m-i}\n({supply[m-1-i]})" for i in range(m)],
                           fontsize=8)
        ax.set_xlabel("Destinations (Consumers)", fontsize=9)
        ax.set_ylabel("Sources (Suppliers)",       fontsize=9)
        fig.tight_layout()

        c = FigureCanvasTkAgg(fig, master=self.right)
        c.draw()
        c.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        plt.close(fig)

# ─────────────────────────────────────────────────────────────────
#  SIMPLEX WINDOW
# ─────────────────────────────────────────────────────────────────
class SimplexWindow(tk.Toplevel):
    def __init__(self, parent):
        super().__init__(parent)
        self.title("EMI — Simplex Method — Linear Programming")
        self.geometry("1050x740")
        self.configure(bg=C_BG)
        self.resizable(True, True)

        hdr = tk.Frame(self, bg=C_HEADER, pady=6)
        hdr.pack(fill=tk.X)
        tk.Label(hdr, text="  Simplex Method — Linear Programming",
                 font=FONT_TITLE, fg=C_TITLE_TXT,
                 bg=C_HEADER).pack(side=tk.LEFT)
        tk.Label(hdr, text="EMI — Fadlaoui Abd-essamade",
                 font=FONT_SMALL, fg="#AAAAAA",
                 bg=C_HEADER).pack(side=tk.RIGHT, padx=12)

        self.paned = tk.PanedWindow(self, orient=tk.HORIZONTAL,
                                    bg=C_BG, sashwidth=6)
        self.paned.pack(fill=tk.BOTH, expand=True, padx=4, pady=4)

        self.left  = tk.Frame(self.paned, bg=C_BG, width=480)
        self.paned.add(self.left, minsize=420)
        self.right = tk.Frame(self.paned, bg=C_BG)
        self.paned.add(self.right, minsize=380)

        self.n_var = tk.StringVar(value="2")
        self.m_var = tk.StringVar(value="3")
        self._build_size_panel()
        self._build_problem()

    def _build_size_panel(self):
        top = tk.Frame(self.left, bg=C_PANEL, relief=tk.GROOVE, bd=2)
        top.pack(fill=tk.X, padx=6, pady=4)
        section_header(top, "  Simplex — Setup",
                        bg=C_ACCENT2).pack(fill=tk.X)

        row = tk.Frame(top, bg=C_PANEL)
        row.pack(pady=6, padx=8)

        tk.Label(row, text="Variables (n):",
                 font=FONT_BODY, bg=C_PANEL, fg=C_LABEL).pack(side=tk.LEFT)
        self.ent_n = tk.Entry(row, textvariable=self.n_var, width=4,
                              font=FONT_BODY, bg=C_ENTRY_BG)
        self.ent_n.pack(side=tk.LEFT, padx=4)

        tk.Label(row, text="Constraints (m):",
                 font=FONT_BODY, bg=C_PANEL, fg=C_LABEL).pack(side=tk.LEFT, padx=(12,0))
        self.ent_m = tk.Entry(row, textvariable=self.m_var, width=4,
                              font=FONT_BODY, bg=C_ENTRY_BG)
        self.ent_m.pack(side=tk.LEFT, padx=4)

        make_button(row, "Build Form", self._build_problem,
                    width=12).pack(side=tk.LEFT, padx=8)

        info = (
            "Maximise c·x  subject to  A·x ≤ b,  x ≥ 0\n\n"
            "Application: Optimal power generation mix\n"
            "  Solar (Noor) / Wind (Tarfaya) / Hydro (Bin El Ouidane)\n"
            "  to maximise revenue subject to capacity & grid constraints."
        )
        tk.Label(top, text=info, font=FONT_SMALL,
                 bg=C_PANEL, fg=C_LABEL,
                 justify=tk.LEFT).pack(padx=8, pady=4)

    def _build_problem(self):
        try:
            n = int(self.n_var.get())
            m = int(self.m_var.get())
        except ValueError:
            messagebox.showerror("Error", "Enter valid integers.")
            return
        if not (1 <= n <= 8 and 1 <= m <= 8):
            messagebox.showerror("Error", "n and m must be between 1 and 8.")
            return

        self.n_val = n
        self.m_val = m

        if hasattr(self, "prob_frame"):
            self.prob_frame.destroy()

        self.prob_frame = tk.Frame(self.left, bg=C_BG)
        self.prob_frame.pack(fill=tk.BOTH, expand=True, padx=6, pady=4)

        section_header(self.prob_frame,
                       "  Enter Objective & Constraints",
                       bg=C_HEADER).pack(fill=tk.X, pady=(0,4))

        var_names = [f"x{i+1}" for i in range(n)]

        # Objective function
        obj_frame = tk.Frame(self.prob_frame, bg=C_BG)
        obj_frame.pack(fill=tk.X, padx=8, pady=4)
        tk.Label(obj_frame, text="Maximise Z = ",
                 font=FONT_BODY, bg=C_BG, fg=C_ACCENT2,
                 width=14).pack(side=tk.LEFT)

        self.obj_entries = []
        for i, vname in enumerate(var_names):
            e = tk.Entry(obj_frame, width=5, font=FONT_MONO,
                         bg="#D5F5E3", justify=tk.CENTER)
            e.insert(0, str(random.randint(3, 15)))
            e.pack(side=tk.LEFT, padx=2)
            tk.Label(obj_frame, text=f"·{vname}",
                     font=FONT_BODY, bg=C_BG, fg=C_LABEL).pack(side=tk.LEFT)
            if i < n-1:
                tk.Label(obj_frame, text="+",
                         font=FONT_BODY, bg=C_BG,
                         fg=C_LABEL).pack(side=tk.LEFT, padx=2)
            self.obj_entries.append(e)

        # Constraints
        c_frame = tk.Frame(self.prob_frame, bg=C_BG)
        c_frame.pack(fill=tk.X, padx=8, pady=4)
        tk.Label(c_frame, text="Constraints  (A·x ≤ b):",
                 font=FONT_BODY, bg=C_BG, fg=C_ACCENT1).pack(anchor=tk.W, pady=2)

        self.con_entries = []  # [row][col] for A
        self.rhs_entries = []  # b

        for i in range(m):
            row_frame = tk.Frame(c_frame, bg=C_BG)
            row_frame.pack(fill=tk.X, pady=1)
            row_entries = []
            for j, vname in enumerate(var_names):
                e = tk.Entry(row_frame, width=5, font=FONT_MONO,
                             bg="#FAD7A0", justify=tk.CENTER)
                e.insert(0, str(random.randint(1, 20)))
                e.pack(side=tk.LEFT, padx=2)
                tk.Label(row_frame, text=f"·{vname}",
                         font=FONT_BODY, bg=C_BG,
                         fg=C_LABEL).pack(side=tk.LEFT)
                if j < n-1:
                    tk.Label(row_frame, text="+",
                             font=FONT_BODY, bg=C_BG,
                             fg=C_LABEL).pack(side=tk.LEFT, padx=2)
                row_entries.append(e)
            tk.Label(row_frame, text=" ≤ ",
                     font=FONT_BODY, bg=C_BG,
                     fg=C_ACCENT1).pack(side=tk.LEFT, padx=4)
            re = tk.Entry(row_frame, width=6, font=FONT_MONO,
                          bg="#D6EAF8", justify=tk.CENTER)
            re.insert(0, str(random.randint(40, 200)))
            re.pack(side=tk.LEFT)
            self.con_entries.append(row_entries)
            self.rhs_entries.append(re)

        # buttons
        btn_row = tk.Frame(self.prob_frame, bg=C_BG)
        btn_row.pack(pady=8)
        make_button(btn_row, "▶  Solve Simplex",
                    self._solve, width=16).pack(side=tk.LEFT, padx=6)
        make_button(btn_row, "🎲  Randomise",
                    self._randomise, bg=C_ACCENT3, width=12).pack(side=tk.LEFT, padx=4)

        # results
        rf, self.result_txt = result_box(self.prob_frame, height=9, width=55)
        rf.pack(fill=tk.BOTH, expand=True, padx=4)

    def _randomise(self):
        n, m = self.n_val, self.m_val
        for e in self.obj_entries:
            e.delete(0, tk.END); e.insert(0, str(random.randint(3,15)))
        for i in range(m):
            for e in self.con_entries[i]:
                e.delete(0, tk.END); e.insert(0, str(random.randint(1,20)))
            self.rhs_entries[i].delete(0, tk.END)
            self.rhs_entries[i].insert(0, str(random.randint(40,200)))

    def _solve(self):
        n, m = self.n_val, self.m_val
        try:
            c_obj = [float(self.obj_entries[i].get()) for i in range(n)]
            A     = [[float(self.con_entries[i][j].get())
                      for j in range(n)] for i in range(m)]
            b     = [float(self.rhs_entries[i].get()) for i in range(m)]
        except ValueError:
            messagebox.showerror("Input Error",
                                 "All fields must contain numbers.")
            return

        status, x, obj_val, log = simplex_maximize(c_obj, A, b)

        self._draw_simplex_chart(c_obj, x, obj_val, status)

        var_names = [f"x{i+1}" for i in range(n)]
        lines = [f"Simplex Method — Linear Programming\n{'='*40}",
                 f"Status         : {status.upper()}"]
        if status == "optimal" and x is not None:
            lines.append(f"Optimal Z      : {obj_val:.4f}  (maximised)")
            lines.append("")
            lines.append("Optimal Solution:")
            for i, (v, val) in enumerate(zip(var_names, x)):
                lines.append(f"  {v} = {val:.4f}")
            lines.append("")
            lines.append("Objective:")
            obj_str = " + ".join(f"{c:.2f}·{v}"
                                  for c, v in zip(c_obj, var_names))
            lines.append(f"  Maximise Z = {obj_str}")
            lines.append("")
            lines.append("Constraints:")
            for i in range(m):
                row_str = " + ".join(f"{A[i][j]:.1f}·{var_names[j]}"
                                      for j in range(n))
                lines.append(f"  {row_str} ≤ {b[i]:.1f}")
        elif status == "unbounded":
            lines.append("  Problem is unbounded — check constraints.")

        lines += ["", "Iteration Log:"]
        lines.extend(log[-15:])  # show last 15 iterations

        lines += ["",
                  "Engineering Context:",
                  "  Optimise MW mix: Solar / Wind / Hydro",
                  "  Subject to: grid capacity, budget, emission caps."]

        write_result(self.result_txt, "\n".join(lines))

    def _draw_simplex_chart(self, c_obj, x, obj_val, status):
        for w in self.right.winfo_children():
            w.destroy()

        if not HAS_PLOT or status != "optimal" or x is None:
            tk.Label(self.right, text="No chart available.",
                     bg=C_BG, fg=C_LABEL, font=FONT_BODY).pack(expand=True)
            return

        n = self.n_val
        var_names = [f"x{i+1}" for i in range(n)]

        fig, axes = plt.subplots(1, 2, figsize=(7, 4.5), facecolor=C_BG)
        fig.suptitle("Simplex — Optimal Solution",
                     fontsize=11, fontweight="bold", color=C_HEADER)

        # Bar chart of solution
        ax1 = axes[0]
        ax1.set_facecolor(C_BG)
        colors = [C_ACCENT1, C_ACCENT2, C_ACCENT3, "#8E44AD",
                  "#1ABC9C", "#2980B9", "#E74C3C", "#F39C12"]
        bars = ax1.bar(var_names, x,
                       color=[colors[i % len(colors)] for i in range(n)],
                       edgecolor="white", linewidth=1.2)
        ax1.set_title("Optimal Values", fontsize=10, color=C_HEADER)
        ax1.set_ylabel("Value", fontsize=9)
        for bar, val in zip(bars, x):
            ax1.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.5,
                     f"{val:.2f}", ha="center", va="bottom", fontsize=8)
        ax1.set_facecolor(C_BG)
        ax1.tick_params(colors=C_LABEL)

        # Contribution to objective
        ax2 = axes[1]
        ax2.set_facecolor(C_BG)
        contribs = [c*xi for c, xi in zip(c_obj, x)]
        wedge_colors = colors[:n]
        if all(c == 0 for c in contribs):
            ax2.text(0.5, 0.5, "Z = 0", ha="center", va="center",
                     fontsize=14, transform=ax2.transAxes, color=C_LABEL)
        else:
            abs_contribs = [abs(c) for c in contribs]
            ax2.pie(abs_contribs, labels=var_names,
                    colors=wedge_colors, autopct="%1.1f%%",
                    startangle=90, textprops={"fontsize": 8})
        ax2.set_title(f"Objective Contribution\nZ* = {obj_val:.3f}",
                      fontsize=10, color=C_HEADER)

        fig.tight_layout()
        c = FigureCanvasTkAgg(fig, master=self.right)
        c.draw()
        c.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        plt.close(fig)

# ─────────────────────────────────────────────────────────────────
#  MAIN APPLICATION WINDOW
# ─────────────────────────────────────────────────────────────────
class MainApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("EMI — Operational Research — Electrical Engineering 2026")
        self.geometry("1000x680")
        self.configure(bg=C_BG)
        self.resizable(True, True)
        self._build()

    def _build(self):
        # ── Top header ──────────────────────────────────────────
        hdr = tk.Frame(self, bg=C_HEADER, pady=8)
        hdr.pack(fill=tk.X)

        left_hdr = tk.Frame(hdr, bg=C_HEADER)
        left_hdr.pack(side=tk.LEFT, padx=16)
        tk.Label(left_hdr,
                 text="EMI — Ecole Mohammadia d'Ingénieurs",
                 font=("Helvetica", 16, "bold"),
                 fg=C_TITLE_TXT, bg=C_HEADER).pack(anchor=tk.W)
        tk.Label(left_hdr,
                 text="Operational Research  |  Electrical Engineering  |  2026",
                 font=FONT_SMALL, fg="#CCCCCC", bg=C_HEADER).pack(anchor=tk.W)
        tk.Label(left_hdr,
                 text="Student: Fadlaoui Abd-essamade       "
                      "Supervisor: Dr. EL MKHALET MOUNA",
                 font=FONT_SMALL, fg="#AAAAAA", bg=C_HEADER).pack(anchor=tk.W)

        # ── Graph generator panel ────────────────────────────────
        self.gen_panel = GraphGeneratorPanel(
            self, on_generate=self._on_graph_generated)
        self.gen_panel.pack(fill=tk.X, padx=10, pady=(8, 0))

        # ── Main preview (graph) ─────────────────────────────────
        preview_lbl = section_header(self,
                                     "  Graph Preview (shared across all algorithms)",
                                     bg=C_HEADER)
        preview_lbl.pack(fill=tk.X, padx=10, pady=(8, 0))

        self.preview_frame = tk.Frame(self, bg=C_BG,
                                      relief=tk.SUNKEN, bd=1)
        self.preview_frame.pack(fill=tk.BOTH, expand=True,
                                padx=10, pady=4)

        # ── Algorithm buttons ─────────────────────────────────────
        btn_outer = tk.Frame(self, bg=C_PANEL,
                             relief=tk.GROOVE, bd=2)
        btn_outer.pack(fill=tk.X, padx=10, pady=(0, 10))
        section_header(btn_outer,
                       "  Select Algorithm",
                       bg=C_HEADER).pack(fill=tk.X)

        btn_grid = tk.Frame(btn_outer, bg=C_PANEL)
        btn_grid.pack(pady=10, padx=10)

        algo_buttons = [
            ("Welsh-Powell\nGraph Colouring",
             lambda: WelshPowellWindow(self), C_ACCENT1),
            ("Kruskal\nMin Spanning Tree",
             lambda: KruskalWindow(self), C_ACCENT1),
            ("Dijkstra\nShortest Path",
             lambda: DijkstraWindow(self), C_ACCENT1),
            ("Bellman-Ford\nShortest Paths",
             lambda: BellmanFordWindow(self), C_ACCENT1),
            ("Ford-Fulkerson\nMax Flow",
             lambda: FordFulkersonWindow(self), C_ACCENT1),
            ("Nord-Ouest\nTransport",
             lambda: TransportWindow(self, "nord_ouest"), C_ACCENT3),
            ("Moindre Coût\nTransport",
             lambda: TransportWindow(self, "moindre_cout"), C_ACCENT3),
            ("Potentiel-MODI\nOptimal Transport",
             lambda: TransportWindow(self, "potentiel"), C_ACCENT3),
            ("Simplex\nLinear Programming",
             lambda: SimplexWindow(self), C_ACCENT2),
        ]

        cols = 5
        for idx, (label, cmd, color) in enumerate(algo_buttons):
            r, c = divmod(idx, cols)
            btn = tk.Button(btn_grid, text=label,
                            command=cmd,
                            bg=color, fg="white",
                            font=FONT_BTN,
                            relief=tk.FLAT, bd=0,
                            activebackground=C_HEADER,
                            activeforeground="white",
                            width=16, height=3,
                            cursor="hand2",
                            wraplength=120)
            btn.grid(row=r, column=c, padx=5, pady=4)

        # ── Status bar ────────────────────────────────────────────
        self.status = tk.Label(self, text="Ready. Generate a graph to begin.",
                               font=FONT_SMALL, fg=C_LABEL,
                               bg=C_PANEL, anchor=tk.W, padx=8)
        self.status.pack(fill=tk.X, side=tk.BOTTOM)

        # initial placeholder
        tk.Label(self.preview_frame,
                 text="Generate a graph using the controls above.\n"
                      "The same graph will be used by all algorithm windows.",
                 font=FONT_BODY, bg=C_BG, fg=C_BORDER,
                 justify=tk.CENTER).pack(expand=True)

    def _on_graph_generated(self):
        draw_graph_on_canvas(
            self.preview_frame,
            title=f"Generated Graph — {len(SHARED.nodes)} Moroccan Substations")
        self.status.config(
            text=f"✔  Graph ready: {len(SHARED.nodes)} nodes, "
                 f"{len(SHARED.edges)} edges. "
                 f"Open any algorithm window to proceed.",
            fg=C_ACCENT2)

# ─────────────────────────────────────────────────────────────────
#  ENTRY POINT
# ─────────────────────────────────────────────────────────────────
if __name__ == "__main__":
    app = MainApp()
    app.mainloop()