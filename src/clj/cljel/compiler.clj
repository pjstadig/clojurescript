;;;; Copyright © Rich Hickey, Paul Stadig. All rights reserved.
;;;;
;;;; The use and distribution terms for this software are covered by the Eclipse
;;;; Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php) which
;;;; can be found in the file epl-v10.html at the root of this distribution.
;;;;
;;;; By using this software in any fashion, you are agreeing to be bound by the
;;;; terms of this license.
;;;;
;;;; You must not remove this notice, or any other, from this software.

(set! *warn-on-reflection* true)

(ns cljel.compiler
  (:refer-clojure :exclude [munge macroexpand-1])
  (:require [clojure.java.io :as io]
            [clojure.string :as string]
            [cljel.tagged-literals :as tags]
            [cljel.analyzer :as ana])
  (:import java.lang.StringBuilder))

(declare munge)

(def js-reserved
  #{"abstract" "boolean" "break" "byte" "case"
    "catch" "char" "class" "const" "continue"
    "debugger" "default" "delete" "do" "double"
    "else" "enum" "export" "extends" "final"
    "finally" "float" "for" "function" "goto" "if"
    "implements" "import" "in" "instanceof" "int"
    "interface" "let" "long" "native" "new"
    "package" "private" "protected" "public"
    "return" "short" "static" "super" "switch"
    "synchronized" "this" "throw" "throws"
    "transient" "try" "typeof" "var" "void"
    "volatile" "while" "with" "yield" "methods"
    "null"})

(def ^:dynamic *position* nil)
(def ^:dynamic *emitted-provides* nil)
(def ^:dynamic *lexical-renames* {})
(def cljel-reserved-file-names #{"deps.cljel"})

(defonce ns-first-segments (atom '#{"cljel" "clojure"}))

(defn munge
  ([s] (munge s js-reserved))
  ([s reserved]
     (if (map? s)
       ;; Unshadowing
       (let [{:keys [name field] :as info} s
             depth (loop [d 0, {:keys [shadow]} info]
                     (cond
                      shadow (recur (inc d) shadow)
                      (@ns-first-segments (str name)) (inc d)
                      :else d))
             renamed (*lexical-renames* (System/identityHashCode s))
             munged-name (munge (cond field (str "self__." name)
                                      renamed renamed
                                      :else name)
                                reserved)]
         (if (or field (zero? depth))
           munged-name
           (symbol (str munged-name "__$" depth))))
       ;; String munging
       (let [ss (string/replace (str s) #"\/(.)" ".$1") ; Division is special
             ss (apply str (map #(if (reserved %) (str % "$") %)
                                (string/split ss #"(?<=\.)|(?=\.)")))
             ms (clojure.lang.Compiler/munge ss)]
         (if (symbol? s)
           (symbol ms)
           ms)))))

(defn- comma-sep [xs]
  (interpose "," xs))

(defn- space-sep [xs]
  (interpose " " xs))

(defn- escape-char [^Character c]
  (let [cp (.hashCode c)]
    (case cp
      ;; Handle printable escapes before ASCII
      34 "\\\""
      92 "\\\\"
      ;; Handle non-printable escapes
      8 "\\b"
      12 "\\f"
      10 "\\n"
      13 "\\r"
      9 "\\t"
      (if (< 31 cp 127)
        c ; Print simple ASCII characters
        (format "\\u%04X" cp))))) ; Any other character is Unicode

(defn- escape-string [^CharSequence s]
  (let [sb (StringBuilder. (count s))]
    (doseq [c s]
      (.append sb (escape-char c)))
    (.toString sb)))

(defn- wrap-in-double-quotes [x]
  (str \" x \"))

(defmulti emit :op)

(defn emits [& xs]
  (doseq [x xs]
    (cond
     (nil? x) nil
     (map? x) (emit x)
     (seq? x) (apply emits x)
     (fn? x)  (x)
     :else (do
             (let [s (print-str x)]
               (when *position*
                 (swap! *position* (fn [[line column]]
                                     [line (+ column (count s))])))
               (print s)))))
  nil)

(defn ^String emit-str [expr]
  (with-out-str (emit expr)))

(defn emitln [& xs]
  (apply emits xs)
  ;; Prints column-aligned line number comments; good test of *position*.
  ;; (when *position*
  ;;   (let [[line column] @*position*]
  ;;     (print (apply str (concat (repeat (- 120 column) \space)
  ;;                               ["// " (inc line)])))))
  (println)
  (when *position*
    (swap! *position* (fn [[line column]]
                        [(inc line) 0])))
  nil)

(defn ^String emit-str [expr]
  (with-out-str (emit expr)))

(defn emit-provide [sym]
  (when-not (or (nil? *emitted-provides*) (contains? @*emitted-provides* sym))
    (swap! *emitted-provides* conj sym)
    (emitln "goog.provide('" (munge sym) "');")))

(defmulti emit-constant class)
(defmethod emit-constant nil [x] (emits "nil"))
(defmethod emit-constant Long [x] (emits x))
;; reader puts Integers in metadata
(defmethod emit-constant Integer [x] (emits x))
(defmethod emit-constant Double [x] (emits x))
(defmethod emit-constant String [x]
  (emits (wrap-in-double-quotes (escape-string x))))
(defmethod emit-constant Boolean [x] (emits (if x "t" "nil")))
(defmethod emit-constant Character [x]
  (emits (wrap-in-double-quotes (escape-char x))))

(defmethod emit-constant java.util.regex.Pattern [x]
  (let [[_ flags pattern] (re-find #"^(?:\(\?([idmsux]*)\))?(.*)" (str x))]
    (emits \/ (.replaceAll (re-matcher #"/" pattern) "\\\\/") \/ flags)))

(defmethod emit-constant clojure.lang.Keyword [x]
  (emits ":" (if (namespace x)
               (str (namespace x) "/") "")
         (name x)))

(defmethod emit-constant clojure.lang.Symbol [x]
  (emits "'" (if (namespace x)
               (str (namespace x) "/") "")
         (name x)))

(defn- emit-meta-constant [x & body]
  (if (meta x)
    (do
      (emits "cljel.core.with_meta(" body ",")
      (emit-constant (meta x))
      (emits ")"))
    (emits body)))

(defmethod emit-constant clojure.lang.PersistentList$EmptyList [x]
  (emit-meta-constant x "cljel.core.List.EMPTY"))

(defmethod emit-constant clojure.lang.PersistentList [x]
  (emit-meta-constant x
                      (concat ["cljel.core.list("]
                              (comma-sep (map #(fn [] (emit-constant %)) x))
                              [")"])))

(defmethod emit-constant clojure.lang.Cons [x]
  (emit-meta-constant x
                      (concat ["cljel.core.list("]
                              (comma-sep (map #(fn [] (emit-constant %)) x))
                              [")"])))

(defmethod emit-constant clojure.lang.IPersistentVector [x]
  (emit-meta-constant x
                      (concat ["cljel.core.vec(["]
                              (comma-sep (map #(fn [] (emit-constant %)) x))
                              ["])"])))

(defmethod emit-constant clojure.lang.IPersistentMap [x]
  (emit-meta-constant x
                      (concat ["cljel.core.hash_map("]
                              (comma-sep (map #(fn [] (emit-constant %))
                                              (apply concat x)))
                              [")"])))

(defmethod emit-constant clojure.lang.PersistentHashSet [x]
  (emit-meta-constant x
                      (concat ["cljel.core.set(["]
                              (comma-sep (map #(fn [] (emit-constant %)) x))
                              ["])"])))

(defmethod emit :no-op [m])

(defmethod emit :var
  [{:keys [info env] :as arg}]
  (let [n (:name info)]
    (when-not (= :statement (:context env))
      (emits (if (= (namespace n) "el")
               (name n)
               (munge info))))))

(defmethod emit :meta
  [{:keys [expr meta env]}]
  (emits "cljel.core.with_meta(" expr "," meta ")"))

(def ^:private array-map-threshold 16)
(def ^:private obj-map-threshold 32)

(defmethod emit :map
  [{:keys [env simple-keys? keys vals]}]
  (cond
   (zero? (count keys))
   (emits "cljel.core.ObjMap.EMPTY")

   (and simple-keys? (<= (count keys) obj-map-threshold))
   (emits "cljel.core.ObjMap.fromObject(["
          (comma-sep keys) ; keys
          "],{"
          (comma-sep (map (fn [k v]
                            (with-out-str
                              (emit k) (print ":") (emit v)))
                          keys vals)) ; js obj
          "})")

   (<= (count keys) array-map-threshold)
   (emits "cljel.core.PersistentArrayMap.fromArrays(["
          (comma-sep keys)
          "],["
          (comma-sep vals)
          "])")

   :else
   (emits "cljel.core.PersistentHashMap.fromArrays(["
          (comma-sep keys)
          "],["
          (comma-sep vals)
          "])")))

(defmethod emit :vector
  [{:keys [items env]}]
  (if (empty? items)
    (emits "cljel.core.PersistentVector.EMPTY")
    (emits "cljel.core.PersistentVector.fromArray(["
           (comma-sep items) "], true)")))

(defmethod emit :set
  [{:keys [items env]}]
  (if (empty? items)
    (emits "cljel.core.PersistentHashSet.EMPTY")
    (emits "cljel.core.PersistentHashSet.fromArray(["
           (comma-sep items) "])")))

(defmethod emit :constant
  [{:keys [form env]}]
  (when-not (= :statement (:context env))
    (emit-constant form)))

(defn get-tag [e]
  (or (-> e :tag)
      (-> e :info :tag)))

(defn infer-tag [e]
  (if-let [tag (get-tag e)]
    tag
    (case (:op e)
      :let (infer-tag (:ret e))
      :if (let [then-tag (infer-tag (:then e))
                else-tag (infer-tag (:else e))]
            (when (= then-tag else-tag)
              then-tag))
      :constant (case (:form e)
                  true 'boolean
                  false 'boolean
                  nil)
      nil)))

(defn safe-test? [e]
  (let [tag (infer-tag e)]
    (or (#{'boolean 'seq} tag)
        (when (= (:op e) :constant)
          (let [form (:form e)]
            (not (or (and (string? form) (= form ""))
                     (and (number? form) (zero? form)))))))))

(defmethod emit :if
  [{:keys [test then else env unchecked]}]
  (let [context (:context env)]
    (emitln "(if " test)
    (emitln then)
    (emitln else ")")))

(defmethod emit :throw
  [{:keys [throw env]}]
  (if (= :expr (:context env))
    (emits "(function(){throw " throw "})()")
    (emitln "throw " throw ";")))

(defn emit-comment
  "Emit a nicely formatted comment string."
  [doc jsdoc]
  (let [docs (when doc [doc])
        docs (if jsdoc (concat docs jsdoc) docs)
        docs (remove nil? docs)]
    (letfn [(print-comment-lines [e] (doseq [next-line (string/split-lines e)]
                                       (emitln ";; " (string/trim next-line))))]
      (when (seq docs)
        (doseq [e docs]
          (when e
            (print-comment-lines e)))))))

(defmethod emit :def
  [{:keys [name init env doc export]}]
  (let [mname (munge name)
        local (gensym)]
    (emit-comment doc (:jsdoc init))
    (when init
      (emitln "(let ((" local " " init "))")
      (emitln "(if (functionp " local ")")
      (emitln "(fset '" mname " " local ")")
      (emits "(setq " mname " " local ")")
      (emits ")")
      (emitln ")"))
    (when-not (= :expr (:context env)) (emitln ""))))

(defn emit-apply-to
  [{:keys [name params env]}]
  (let [arglist (gensym "arglist__")
        delegate-name (str (munge name) "__delegate")
        params (map munge params)]
    (emitln "(function (" arglist "){")
    (doseq [[i param] (map-indexed vector (butlast params))]
      (emits "var " param " = cljel.core.first(")
      (dotimes [_ i] (emits "cljel.core.next("))
      (emits arglist ")")
      (dotimes [_ i] (emits ")"))
      (emitln ";"))
    (if (< 1 (count params))
      (do
        (emits "var " (last params) " = cljel.core.rest(")
        (dotimes [_ (- (count params) 2)] (emits "cljel.core.next("))
        (emits arglist)
        (dotimes [_ (- (count params) 2)] (emits ")"))
        (emitln ");")
        (emitln "return " delegate-name "(" (string/join ", " params) ");"))
      (do
        (emits "var " (last params) " = ")
        (emits "cljel.core.seq(" arglist ");")
        (emitln ";")
        (emitln "return " delegate-name "(" (string/join ", " params) ");")))
    (emits "})")))

(defn emit-fn-method
  [{:keys [type name variadic params expr env recurs max-fixed-arity]}]
  (when name
    (emitln "(let ((" name " nil))")
    (emitln "(fset '" name " "))
  (emitln"(lambda (" (space-sep (map munge params)) ")")
  (when type
    (emitln "var self__ = this;"))
  (when recurs
    (emitln "(catch 'break")
    (emitln "(while t")
    (emitln "(catch 'continue"))
  (let [rname (gensym)]
    (emits "(let ((" rname " ")
    (emits expr)
    (emitln "))")
    (if recurs
      (do (emitln "(throw 'break " rname ")")
          (emitln ")")
          (emitln ")")
          (emitln ")"))
      (emitln rname)))
  (emitln ")")
  (emitln ")")
  (when name
    (emitln ")")
    (emitln "(function " name ")")
    (emitln ")")))

(defn emit-variadic-fn-method
  [{:keys [type name variadic params expr env recurs max-fixed-arity] :as f}]
  (let [named? name
        name (or name (gensym))
        mname (munge name)
        params (map munge params)]
    (when named?
      (emitln "(let ((" name " nil))")
      (emitln "(fset '" name " "))
    (emitln "(lambda (" (space-sep
                         (concat (butlast params)
                                 ['&rest (last params)])) ")")
    (when type
      (emitln "var self__ = this;"))
    (when recurs
      (emitln "(catch 'break")
      (emitln "(while t")
      (emitln "(catch 'continue"))
    (let [rname (gensym)]
      (emits "(let ((" rname " ")
      (emits expr)
      (emitln "))")
      (if recurs
        (do (emitln "(throw 'break " rname ")")
            (emitln ")")
            (emitln ")")
            (emitln ")"))
        (emitln rname))
      (emitln ")"))
    (emitln ")")
    (when named?
      (emitln ")")
      (emitln "(function " mname ")")
      (emitln ")"))))

(defmethod emit :fn
  [{:keys [name env methods max-fixed-arity variadic recur-frames loop-lets]}]
  ;;fn statements get erased, serve no purpose and can pollute scope if named
  (when-not (= :statement (:context env))
    (let [loop-locals (->> (concat (mapcat :params (filter #(and % @(:flag %))
                                                           recur-frames))
                                   (mapcat :params loop-lets))
                           (map munge)
                           seq)]
      (when loop-locals
        (when (= :return (:context env))
          (emits "return "))
        (emitln "((function (" (comma-sep (map munge loop-locals)) "){")
        (when-not (= :return (:context env))
          (emits "return ")))
      (if (= 1 (count methods))
        (if variadic
          (emit-variadic-fn-method (assoc (first methods) :name name))
          (emit-fn-method (assoc (first methods) :name name)))
        (let [has-name? (and name true)
              name (or name (gensym))
              mname (munge name)
              maxparams (map munge (apply max-key count (map :params methods)))
              mmap (into {}
                         (map (fn [method]
                                [(munge (symbol (str mname "__"
                                                     (count (:params method)))))
                                 method])
                              methods))
              ms (sort-by #(-> % second :params count) (seq mmap))]
          (emitln "(let (")
          (emitln "(" mname " nil)")
          (doseq [[n meth] ms]
            (emitln "(" n " nil)"))
          (emitln ")")
          (doseq [[n meth] ms]
            (emits "(fset '" n " ")
            (if (:variadic meth)
              (emit-variadic-fn-method meth)
              (emit-fn-method meth))
            (emitln ")"))
          (let [args (gensym)]
            (emitln "(fset '" mname " (lambda (&rest " args ")")
            (emitln "(cond")
            (doseq [[n meth] ms]
              (if (:variadic meth)
                (do (emitln "((>= (length " args ") " (count maxparams) ")")
                    (emitln "(apply (function " n ") " args "))"))
                (let [pcnt (count (:params meth))]
                  (emitln "((eq (length " args ") " pcnt ")")
                  (emitln "(apply (function " n ") " args "))"))))
            (emitln "(t (throw 'arity-error (format \"Invalid arity: %d\""
                    " (length " args "))))"))
          (emitln ")")
          (emitln ")")
          (emitln ")")
          (when variadic
            (emitln "(put '" mname " 'cljel$lang$maxFixedArity " max-fixed-arity
                    ")"))
          (when has-name?
            (doseq [[n meth] ms]
              (let [c (count (:params meth))]
                (if (:variadic meth)
                  (emitln "(put '" mname
                          " 'cljel$lang$arity$variadic (function " n "))")
                  (emitln "(put '" mname " 'cljel$lang$arity$" c
                          " (function " n "))")))))
          (emitln "(function " mname ")")
          (emitln ")")))
      (when loop-locals
        (emitln ";})(" (comma-sep loop-locals) "))")))))

(defmethod emit :do
  [{:keys [statements ret env]}]
  (let [context (:context env)]
    (emitln "(progn")
    (when statements
      (emits statements))
    (emit ret)
    (emitln ")")))

(defmethod emit :try*
  [{:keys [env try catch name finally]}]
  (let [context (:context env)
        ret (gensym "ret")
        ex (gensym "ex")]
    (emits "(unwind-protect\n"
           "(condition-case " ex "\n"
           try
           "(" name " \n"
           ;; "(message (format \"Caught: [%s]\" " ex "))\n"
           catch "))\n"
           finally ")\n")))

(defn emit-let
  [{:keys [bindings expr env]} is-loop]
  (let [context (:context env)]
    (emits "(let (")
    (binding [*lexical-renames* (into *lexical-renames*
                                      (when (= :statement context)
                                        (map #(vector
                                               (System/identityHashCode %)
                                               (gensym (str (:name %) "-")))
                                             bindings)))]
      (doseq [{:keys [init] :as binding} bindings]
        (emitln "(" (munge binding) " " init ")"))
      (emitln ")")
      (when is-loop
        (emitln "(catch 'break")
        (emitln "(while t")
        (emitln "(catch 'continue"))
      (let [rname (gensym)]
        (emits "(let ((" rname " ")
        (emits expr)
        (emitln "))")
        (if is-loop
          (do (emits "(throw 'break " rname ")")
              (emits ")")
              (emits ")")
              (emits ")"))
          (emitln rname))
        (emitln ")")))
    (emitln ")")))

(defmethod emit :let [ast]
  (emit-let ast false))

(defmethod emit :loop [ast]
  (emit-let ast true))

(defmethod emit :recur
  [{:keys [frame exprs env]}]
  (let [temps (vec (take (count exprs) (repeatedly gensym)))
        params (:params frame)]
    (emits "(let (")
    (dotimes [i (count exprs)]
      (emitln "(" (temps i) " " (exprs i) ")"))
    (emitln ")")
    (dotimes [i (count exprs)]
      (emitln "(setq " (munge (params i)) " " (temps i) ")"))
    (emitln "(throw 'continue nil)")
    (emitln ")")))

(defmethod emit :letfn
  [{:keys [bindings expr env]}]
  (let [context (:context env)]
    (emits "(let (")
    (doseq [{:keys [init] :as binding} bindings]
      (emitln "(" (munge binding) " nil)"))
    (emitln ")")
    (doseq [{:keys [init] :as binding} bindings]
      (emitln "(fset '" (munge binding) " " (dissoc init :name) ")"))
    (emits expr)
    (emitln ")")))

(defn protocol-prefix [psym]
  (symbol (str (-> (str psym) (.replace \. \$) (.replace \/ \$)) "$")))

(defmethod emit :invoke
  [{:keys [f args env] :as expr}]
  (let [info (:info f)
        fn? (and ana/*cljel-static-fns*
                 (not (:dynamic info))
                 (:fn-var info))
        protocol (:protocol info)
        proto? (let [tag (infer-tag (first (:args expr)))]
                 (and protocol tag
                      (or ana/*cljel-static-fns*
                          (:protocol-inline env))
                      (or (= protocol tag)
                          (when-let [ps (:protocols (ana/resolve-existing-var
                                                     (dissoc env :locals) tag))]
                            (ps protocol)))))
        opt-not? (and (= (:name info) 'cljel.core/not)
                      (= (infer-tag (first (:args expr))) 'boolean))
        ns (:ns info)
        js? (= ns 'js)
        goog? (when ns
                (or (= ns 'goog)
                    (when-let [ns-str (str ns)]
                      (= (get (string/split ns-str #"\.") 0 nil) "goog"))))
        keyword? (and (= (-> f :op) :constant)
                      (keyword? (-> f :form)))
        [f variadic-invoke]
        (if fn?
          (let [arity (count args)
                variadic? (:variadic info)
                mps (:method-params info)
                mfa (:max-fixed-arity info)]
            (cond
             ;; if only one method, no renaming needed
             (and (not variadic?)
                  (= (count mps) 1))
             [f nil]

             ;; direct dispatch to variadic case
             (and variadic? (> arity mfa))
             [(update-in f [:info :name]
                         (fn [name]
                           (symbol (str (munge name)
                                        ".cljel$lang$arity$variadic"))))
              {:max-fixed-arity mfa}]

             ;; direct dispatch to specific arity case
             :else
             (let [arities (map count mps)]
               (if (some #{arity} arities)
                 [(update-in f [:info :name]
                             (fn [name]
                               (symbol (str (munge name)
                                            ".cljel$lang$arity$" arity))))
                  nil]
                 [f nil]))))
          [f nil])]
    (cond
     opt-not?
     (emits "!(" (first args) ")")

     proto?
     (let [pimpl (str (munge (protocol-prefix protocol))
                      (munge (name (:name info))) "$arity$"
                      (count args))]
       (emits (first args) "." pimpl "(" (comma-sep args) ")"))

     keyword?
     (emits "(new cljel.core.Keyword(" f ")).call("
            (comma-sep (cons "null" args))
            ")")

     variadic-invoke
     (let [mfa (:max-fixed-arity variadic-invoke)]
       (emits f "(" (comma-sep (take mfa args))
              (when-not (zero? mfa) ",")
              "cljel.core.array_seq([" (comma-sep (drop mfa args))
              "], 0))"))

     (or fn? js? goog?)
     (emits f "(" (comma-sep args)  ")")

     :else
     (if (and ana/*cljel-static-fns* (= (:op f) :var))
       (let [fprop (str ".cljel$lang$arity$" (count args))]
         (emits "(" f fprop " ? " f fprop "(" (comma-sep args) ") : "
                f ".call(" (comma-sep (cons "null" args)) "))"))
       (emitln "(" f " " (space-sep args) ")")))))

(defmethod emit :new
  [{:keys [ctor args env]}]
  (emits "(new " ctor "("
         (comma-sep args)
         "))"))

(defmethod emit :set!
  [{:keys [target val env]}]
  (emits "(setq " target " " val ")\n"))

(defmethod emit :ns
  [{:keys [name requires uses requires-macros env]}]
  (swap! ns-first-segments conj (first (string/split (str name) #"\.")))
  (emitln "goog.provide('" (munge name) "');")
  (when-not (= name 'cljel.core)
    (emitln "goog.require('cljel.core');"))
  (doseq [lib (into (vals requires) (distinct (vals uses)))]
    (emitln "goog.require('" (munge lib) "');")))

(defmethod emit :deftype*
  [{:keys [t fields pmasks]}]
  (let [fields (map munge fields)]
    (emit-provide t)
    (emitln "")
    (emitln "/**")
    (emitln "* @constructor")
    (emitln "*/")
    (emitln (munge t) " = (function (" (comma-sep fields) "){")
    (doseq [fld fields]
      (emitln "this." fld " = " fld ";"))
    (doseq [[pno pmask] pmasks]
      (emitln "this.cljel$lang$protocol_mask$partition" pno "$ = " pmask ";"))
    (emitln "})")))

(defmethod emit :defrecord*
  [{:keys [t fields pmasks]}]
  (let [fields (concat (map munge fields) '[__meta __extmap])]
    (emit-provide t)
    (emitln "")
    (emitln "/**")
    (emitln "* @constructor")
    (doseq [fld fields]
      (emitln "* @param {*} " fld))
    (emitln "* @param {*=} __meta ")
    (emitln "* @param {*=} __extmap")
    (emitln "*/")
    (emitln (munge t) " = (function (" (comma-sep fields) "){")
    (doseq [fld fields]
      (emitln "this." fld " = " fld ";"))
    (doseq [[pno pmask] pmasks]
      (emitln "this.cljel$lang$protocol_mask$partition" pno "$ = " pmask ";"))
    (emitln "if(arguments.length>" (- (count fields) 2) "){")
    (emitln "this.__meta = __meta;")
    (emitln "this.__extmap = __extmap;")
    (emitln "} else {")
    (emits "this.__meta=")
    (emit-constant nil)
    (emitln ";")
    (emits "this.__extmap=")
    (emit-constant nil)
    (emitln ";")
    (emitln "}")
    (emitln "})")))

(defmethod emit :dot
  [{:keys [target field method args env]}]
  (if field
    (emits target "." (munge field #{}))
    (emits target "." (munge method #{}) "("
           (comma-sep args)
           ")")))

(defmethod emit :js
  [{:keys [env code segs args]}]
  (if code
    (emits code)
    (emits (interleave (concat segs (repeat nil))
                       (concat args [nil])))))

(defn forms-seq
  "Seq of forms in a Clojure or ClojureScript file."
  ([f]
     (forms-seq f (clojure.lang.LineNumberingPushbackReader. (io/reader f))))
  ([f ^java.io.PushbackReader rdr]
     (if-let [form (binding [*ns* ana/*reader-ns*] (read rdr nil nil))]
       (lazy-seq (cons form (forms-seq f rdr)))
       (.close rdr))))

(defn rename-to-el
  "Change the file extension from .cljel to .js. Takes a File or a
  String. Always returns a String."
  [file-str]
  (clojure.string/replace file-str #"\.cljel$" ".el"))

(defn mkdirs
  "Create all parent directories for the passed file."
  [^java.io.File f]
  (.mkdirs (.getParentFile (.getCanonicalFile f))))

(defmacro with-core-cljel
  "Ensure that core.cljel has been loaded."
  [& body]
  `(do (when-not (:defs (get @ana/namespaces 'cljel.core))
         (ana/analyze-file "cljel/core.cljel"))
       ~@body))

(defn compile-file* [src dest]
  (with-core-cljel
    (with-open [out ^java.io.Writer (io/make-writer dest {})]
      (binding [*out* out
                ana/*cljel-ns* 'cljel.user
                ana/*cljel-file* (.getPath ^java.io.File src)
                *data-readers* tags/*cljel-data-readers*
                *position* (atom [0 0])
                *emitted-provides* (atom #{})]
        (emitln ";; lexical-binding: t")
        (loop [forms (forms-seq src)
               ns-name nil
               deps nil]
          (if (seq forms)
            (let [env (ana/empty-env)
                  ast (ana/analyze env (first forms))]
              (do (emit ast)
                  (if (= (:op ast) :ns)
                    (recur (rest forms) (:name ast) (merge (:uses ast)
                                                           (:requires ast)))
                    (recur (rest forms) ns-name deps))))
            {:ns (or ns-name 'cljel.user)
             :provides [ns-name]
             :requires (if (= ns-name 'cljel.core) (set (vals deps))
                           (conj (set (vals deps)) 'cljel.core))
             :file dest}))))))

(defn requires-compilation?
  "Return true if the src file requires compilation."
  [^java.io.File src ^java.io.File dest]
  (or (not (.exists dest))
      (> (.lastModified src) (.lastModified dest))))

(defn parse-ns [src dest]
  (with-core-cljel
    (binding [ana/*cljel-ns* 'cljel.user]
      (loop [forms (forms-seq src)]
        (if (seq forms)
          (let [env (ana/empty-env)
                ast (ana/analyze env (first forms))]
            (if (= (:op ast) :ns)
              (let [ns-name (:name ast)
                    deps    (merge (:uses ast) (:requires ast))]
                {:ns (or ns-name 'cljel.user)
                 :provides [ns-name]
                 :requires (if (= ns-name 'cljel.core)
                             (set (vals deps))
                             (conj (set (vals deps)) 'cljel.core))
                 :file dest})
              (recur (rest forms)))))))))

(defn compile-file
  "Compiles src to a file of the same name, but with a .js extension,
   in the src file's directory.

   With dest argument, write file to provided location. If the dest
   argument is a file outside the source tree, missing parent
   directories will be created. The src file will only be compiled if
   the dest file has an older modification time.

   Both src and dest may be either a String or a File.

   Returns a map containing {:ns .. :provides .. :requires .. :file ..}.
   If the file was not compiled returns only {:file ...}"
  ([src]
     (let [dest (rename-to-el src)]
       (compile-file src dest)))
  ([src dest]
     (let [src-file (io/file src)
           dest-file (io/file dest)]
       (if (.exists src-file)
         (if (requires-compilation? src-file dest-file)
           (do (mkdirs dest-file)
               (compile-file* src-file dest-file))
           (parse-ns src-file dest-file))
         (throw (java.io.FileNotFoundException.
                 (str "The file " src " does not exist.")))))))

(defn path-seq
  [file-str]
  (->> java.io.File/separator
       java.util.regex.Pattern/quote
       re-pattern
       (string/split file-str)))

(defn to-path
  ([parts]
     (to-path parts java.io.File/separator))
  ([parts sep]
     (apply str (interpose sep parts))))

(defn to-target-file
  "Given the source root directory, the output target directory and
  file under the source root, produce the target file."
  [^java.io.File dir ^String target ^java.io.File file]
  (let [dir-path (path-seq (.getAbsolutePath dir))
        file-path (path-seq (.getAbsolutePath file))
        relative-path (drop (count dir-path) file-path)
        parents (butlast relative-path)
        parent-file (java.io.File. ^String (to-path (cons target parents)))]
    (java.io.File. parent-file ^String (rename-to-el (last relative-path)))))

(defn cljel-files-in
  "Return a sequence of all .cljel files in the given directory."
  [dir]
  (filter #(let [name (.getName ^java.io.File %)]
             (and (.endsWith name ".cljel")
                  (not= \. (first name))
                  (not (contains? cljel-reserved-file-names name))))
          (file-seq dir)))

(defn compile-root
  "Looks recursively in src-dir for .cljel files and compiles them to
   .js files. If target-dir is provided, output will go into this
   directory mirroring the source directory structure. Returns a list
   of maps containing information about each file which was compiled
   in dependency order."
  ([src-dir]
     (compile-root src-dir "out"))
  ([src-dir target-dir]
     (let [src-dir-file (io/file src-dir)]
       (loop [cljel-files (cljel-files-in src-dir-file)
              output-files []]
         (if (seq cljel-files)
           (let [cljel-file (first cljel-files)
                 output-file ^java.io.File (to-target-file src-dir-file
                                                           target-dir
                                                           cljel-file)
                 ns-info (compile-file cljel-file output-file)]
             (recur (rest cljel-files)
                    (conj output-files
                          (assoc ns-info
                            :file-name (.getPath output-file)))))
           output-files)))))
