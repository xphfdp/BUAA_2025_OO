import java.util.HashMap;
import java.util.HashSet;

public class DisjointSet {
    private static HashMap<Integer, Integer> parent;
    private static HashMap<Integer, Integer> rank;
    private static HashMap<Integer, HashSet<Integer>> edges;

    public DisjointSet() {
        parent = new HashMap<>();
        rank = new HashMap<>();
        edges = new HashMap<>();
    }

    public void makeSet(int id) {
        if (!parent.containsKey(id)) {
            parent.put(id, id);
            rank.put(id, 0);
        }
    }

    public int find(int id) {
        int root = id;
        while (root != parent.get(root)) {
            root = parent.get(root);
        }

        int now = id;
        while (now != root) {
            int next = parent.get(now);
            parent.put(now, root);
            now = next;
        }
        return root;
    }

    public void merge(int id1, int id2) {
        int root1 = find(id1);
        int root2 = find(id2);
        if (root1 == root2) {
            return;
        }
        int rank1 = rank.get(root1);
        int rank2 = rank.get(root2);
        if (rank1 > rank2) {
            parent.put(root2, root1);
        } else if (rank1 < rank2) {
            parent.put(root1, root2);
        } else {
            parent.put(root2, root1);
            rank.put(root1, rank1 + 1);
        }
    }

    public void addEdge(int id1, int id2) {
        int max = Math.max(id1, id2);
        int min = Math.min(id1, id2);
        if (edges.containsKey(min)) {
            edges.get(min).add(max);
        } else {
            HashSet<Integer> nodes = new HashSet<>();
            nodes.add(max);
            edges.put(min, nodes);
        }
    }

    public void removeEdge(int id1, int id2) {
        int max = Math.max(id1, id2);
        int min = Math.min(id1, id2);
        HashSet<Integer> nodes = edges.get(min);
        nodes.remove(max);
        if (nodes.isEmpty()) {
            edges.remove(min, nodes);
        }
    }

    public void initReset() {
        parent.clear();
        rank.clear();
    }

    public void reset() {
        for (int id1 : edges.keySet()) {
            for (int id2 : edges.get(id1)) {
                merge(id1, id2);
            }
        }
    }
}
