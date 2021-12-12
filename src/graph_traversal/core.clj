(ns graph-traversal.core
  (:gen-class))

(def G
  "The graph structure is a map of nodes to a list of neighbors.
  So { :1 [:2 :3] } means :1 has two edges – one to :2 and one to :3"
  {:1 [:2 :3]
   :2 [:4]
   :3 [:4]
   :4 []})

(defn traverse-graph-dfs [graph node]
  (loop [frontier [node]  ; node to explore next
         explored #{node} ; explored set
         vertices []]     ; vertices explored in sequence
    (if (empty? frontier) ; if frontier is empty, we explored all nodes
      vertices
      (let [curr     (peek frontier) ; get last node insert into the stack (LIFO)
            adiacent (curr graph)]   ; get adiacent node
        (recur
         (into                        ; put into frontier the unexplored adiacent nodes
          (pop frontier)              ; remove current element from frontier
          (remove explored adiacent)) ; remove from adiacent the already explored
         (into explored adiacent)     ; add adiacent to explored set (if no present)
         (conj vertices curr))))))    ; add current node to explored vertices

(defn seq-graph-dfs [graph node]
  ((fn rec-dfs [explored frontier]
     (lazy-seq
      (if (empty? frontier)
        nil
        (let [curr (peek frontier)
              adiacent (curr graph)]
          (cons curr (rec-dfs
                      (into explored adiacent)
                      (into (pop frontier) (remove explored adiacent))))))))
   #{node} [node]))

(defn seq-graph-bfs [graph node]
  ((fn rec-bfs [explored frontier]
     (lazy-seq
      (if (empty? frontier)
        nil
        (let [curr (peek frontier)
              adiacent (graph curr)]
          (cons curr (rec-bfs
                      (into explored adiacent)
                      (into (pop frontier) (remove explored adiacent))))))))
   ;; Used a queue for FIFO
   #{node} (conj (clojure.lang.PersistentQueue/EMPTY) node)))

(traverse-graph-dfs G :1)
(seq-graph-dfs G :1)
(seq-graph-bfs G :1)

(defn seq-graph [d g s]
  ((fn rec-seq [explored frontier]
     (lazy-seq
      (if (empty? frontier)
        nil
        (let [v (peek frontier)
              neighbors (g v)]
          (cons v (rec-seq
                   (into explored neighbors)
                   (into (pop frontier) (remove explored neighbors))))))))
   #{s} (conj d s)))

(def seq-graph-dfs (partial seq-graph []))
(def seq-graph-bfs (partial seq-graph (clojure.lang.PersistentQueue/EMPTY)))

(seq-graph-dfs G :1) ; => (:1 :3 :4 :2)
(seq-graph-bfs G :1) ; => (:1 :2 :3 :4)

;; 1. Extend the graph definition to include a weight between graph edges

(def graph
  {:1 {:2 1 :3 2}
   :2 {:4 4}
   :3 {:4 2}
   :4 {}})

;; 2. Write an algorithm to randomly generate a simple directed graph using your answer from #1

(def ^:dynamic *max-weight* 10)

(defn- create-vertices [n]
  (let [create-vertex #(-> (str %)
                           (keyword)
                           (hash-map {}))]
    (reduce
     #(->> (inc %2)         ; range starts from 0, vertices from 1
           (create-vertex)  ; create an empty vertex {:n {}}
           (into %1))       ; merge it into the graph
     {}
     (range n))))           ; create n vertices

(defn- random-edges [g s]
  (loop [graph  g
         sparse s]
    (if (zero? sparse)
      graph
      (let [nodes  (shuffle (keys graph))
            src    (first nodes)
            dst    (last nodes)
            weigth (rand-int *max-weight*)]
        (recur
         (assoc-in graph [src dst] weigth)
         (dec sparse))))))

(defn make-graph
  "Generate a random directed acyclic graph.
   
  n - size of generated graph (vertices).
  s - sparsness or number of directed edges."
  [n s]
  (if (and (int? n) (int? s)
           (>= s (- n 1))
           (<= s (* n (- n 1))))
    (let [g     (create-vertices n)
          nodes (shuffle (keys g))]
      (loop [graph    g
             sparse    s
             connected (list (first nodes))
             isolated  (rest nodes)]
        (if (empty? isolated)
         ;; Add additional random edges
          (random-edges graph sparse)
         ;; Create random edges from connected to isolated
          (let [src (rand-nth connected)
                dst (rand-nth isolated)
                w   (rand-int *max-weight*)]
            (recur
             (assoc-in graph [src dst] w)
             (dec s)
             (conj connected dst)
             (remove #(= % dst) isolated))))))
    (throw
     (Exception.
      "Number of directed edges should be between n-1 and n*(n-1)."))))

(defn parse-int [s]
  (Integer. (re-find  #"\d+" s)))

(defn- sort-keys [node]
  (sort-by #(parse-int (name %)) (keys node)))

(defn pprint-graph
  ([graph] 
   (pprint-graph graph false))
  ([graph sort?]
   (loop [ordered-keys (if sort? (sort-keys graph) (keys graph))]
    (when-not (empty? ordered-keys)
      (let [node-k (first ordered-keys)
            node   (node-k graph)]
        (doseq [neigh-k (if sort? (sort-keys node) (keys node))]
          (println (str node-k " => " neigh-k " (" (neigh-k node) ")")))
        (recur (rest ordered-keys)))))))

;; Write an implementation of Dijkstra's algorithm that traverses your graph and outputs the shortest path between any 2 randomly selected vertices.

(def ^:private inf ##Inf)

(defn get-weight [path node]
  (get-in path [node :w] inf))

(defn- get-cheapest-node
  [source-frontier path]
  (loop [frontier        source-frontier
         cheapest-node   -1
         cheapest-weight inf]
    (if (empty? frontier)
      cheapest-node
      (let [node   (peek frontier)
            weight (get-weight path node)
            fr     (pop frontier)]
          (if (or (= -1 cheapest-node) (< weight cheapest-weight))
            (recur fr node weight)
            (recur fr cheapest-node cheapest-weight))))))

(defn- next-path
  [graph source-frontier cheapest-node current-path]
  (loop [frontier source-frontier
         path current-path]
    (if (empty? frontier)
      path
      (let [node            (peek frontier)
            curr            (get-weight path node)
            cheapest-weight (get-weight path cheapest-node)
            node-weight     (or (node (cheapest-node graph)) inf)
            prev-w          (min curr (+ cheapest-weight node-weight))]
        (recur
         (pop frontier)
         (-> (if (= curr prev-w)
               path
               (assoc-in path [node :parent] cheapest-node) )
             (assoc-in [node :w] prev-w)))))))

(defn- dijkstra
  [graph source]
  (let [source-path {source {:w 0 :parent nil}}
        source-edges (-> (map
                          (fn [[k w]]
                            {k {:w w :parent source}})
                          (source graph)) 
                         (vec))]
    (loop [path     (apply merge source-path source-edges)
           frontier (-> (dissoc graph source) keys vec)]
      ;; (prn frontier path)
      (if (empty? frontier)
        path
        (let [cheapest-node (get-cheapest-node frontier path)
              new-frontier  (-> (remove #(= % cheapest-node) frontier) vec)]
          (recur
           (next-path graph new-frontier cheapest-node path)
           new-frontier))))))

(defn- walk-back
  [paths source dest]
  (loop [shortest (list dest)
         curr     dest]
    (let [parent    (:parent (curr paths))
          new-paths (conj shortest parent)]
       (condp = parent
         nil    ()        ; empty
         source new-paths ; shortest-path
         (recur new-paths parent))))) ; keep walking backwards

(defn shortest-path
  "Uses Dijkstra's algorithm that traverses a DAG and outputs the shortest
   path between 2 vertices."
  [graph source dest]
  (-> (dijkstra graph source)
      (walk-back source dest)))

(comment
  (let [g (make-graph 10 10)]
    (shortest-path g (first (keys g)) (last (keys g)))))

;; Write a suite of functions to calculate distance properties for your graph.

(defn- walker
  [graph source select compare-node init-acc]
  ((fn rec-traverse
    [explored frontier acc]
    (if (empty? frontier)
      acc
      (let [vertex (peek frontier)
            neighbors (->> (vertex graph) (keys) vec)
            new-acc (select graph source vertex)]
        (rec-traverse
         (into explored neighbors)
         (into (pop frontier) (remove explored neighbors))
         (compare-node new-acc acc)))))
   #{source}
   (conj (clojure.lang.PersistentQueue/EMPTY) source)
   init-acc))

(defn eccentricity
  "The eccentricity of a vertex v is defined as the greatest distance between v and any other vertex."
  [graph source]
  (let [distance-fn (fn [g source vertex] 
                      (-> (shortest-path g source vertex)
                          (count)
                          (dec)))]
    (walker graph source distance-fn max 0)))

(defn- eccentricity-graph
  [graph f init-acc]
  (let [source (-> (keys graph) (first))
        select (fn [g _ vertex]
                 (eccentricity g vertex))]
    (walker graph source select f init-acc)))

(defn radius
  "The radius of a graph is the minimum eccentricity of any vertex in a graph."
  [graph]
  (let [comp #(-> (min %1 %2)
                  (max 1))]
    (eccentricity-graph graph comp inf)))

(defn diameter
  "The diameter of a graph is the maximum eccentricity of any vertex in a graph."
  [graph]
  (eccentricity-graph graph max 0))

(comment
  (let [g (make-graph 10 10)]
    (eccentricity g (first (keys g))) 
    (radius g)
    (diameter g)))

(defn -main
  "I don't do a whole lot ... yet."
  [& args]
  (println "Hello, World!"))
