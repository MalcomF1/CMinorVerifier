/*
    TODO: 这是你唯一允许编辑的文件，你可以对此文件作任意的修改，只要整个项目可以正常地跑起来。
*/
using System.Collections.Generic;
using System.IO;

namespace cminor
{
    /// <summary> 一个验证器，接受一个中间表示，判断其是否有效。 </summary>
    class Verifier
    {
        SMTSolver solver = new SMTSolver();
        TextWriter writer;
        Dictionary<Location, List<List<Location>>> visitedLocsPathMap = new Dictionary<Location, List<List<Location>>>();
        int enterTimes;

        public Verifier(TextWriter writer)
        {
            this.writer = writer;
        }

        /// <summary> 应用此验证器 </summary>
        /// <param name="cfg"> 待验证的控制流图 </param>
        /// <returns> 验证结果 </returns>
        /// <list type="bullet">
        ///     <item> “&gt; 0” 表示所有的 specification 都成立 </item>
        ///     <item> “&lt; 0” 表示有一个 specification 不成立 </item>
        ///     <item> “= 0” 表示 unknown </item>
        /// </list>
        public int Apply(IRMain cfg)
        {
            /// remarks: ACSL语法支持自定义谓词。输入的程序中就可能定义了一些谓词，这里先把他们注册给Solver，后续就不需要特殊的处理
            foreach (Predicate predicate in cfg.predicates)
            {
                solver.definePredicate(predicate);
            }

            // YOUR CODE HERE
            // 根据演绎验证的原理，生成基本路径和验证条件，交由后端Solver求解
            foreach (Function function in cfg.functions)
            {
                EntryLocation entry = function.entryLocation;

                // find all basic paths.
                List<List<Location>> allBasicPaths = findAllBasicPaths(entry);

                foreach (List<Location> basicPath in allBasicPaths)
                {
                    int startIndex = basicPath.Count-2;
                    Expression currCond = null;

                    // last location is before function call statement.
                    if (basicPath.Count >= 2 && basicPath[basicPath.Count-1] == basicPath[basicPath.Count-2])
                    {
                        Location funcPredLoc = basicPath[basicPath.Count-3];
                        Location funcPostLoc = basicPath[basicPath.Count-2];
                        FunctionCallStatement stmt = funcPredLoc.succStatements[funcPredLoc.succLocations.IndexOf(funcPostLoc)] as FunctionCallStatement;
                        Expression funcPreCondition = convertCondList2SingleCond(stmt.rhs.function.entryLocation.conditions);
                        for (int i = 0; i < stmt.rhs.argumentVariables.Count; i++)
                        {
                            funcPreCondition = funcPreCondition.Substitute(stmt.rhs.function.parameters[i], new VariableExpression(stmt.rhs.argumentVariables[i]));
                        }
                        currCond = funcPreCondition;
                        startIndex = basicPath.Count - 4;
                    }

                    // last location is exit location.
                    else if (basicPath[basicPath.Count-1] is ExitLocation exitLoc)
                    {
                        currCond = convertCondList2SingleCond(exitLoc.conditions);
                    }

                    // last location is loop head.
                    else if (basicPath[basicPath.Count-1] is LoopHeadLocation loopHeadLoc)
                    {
                        currCond = convertCondList2SingleCond(loopHeadLoc.invariants);
                    }

                    // calculate wlp expression for each basic path. If any is invalid, then returns UNVERIFIED.
                    Expression wlpExp = calculateWlp(basicPath, currCond, startIndex);
                    if (solver.CheckValid(wlpExp) is not null)
                    {
                        return -1;
                    }

                    // check whether the ranking function is valid for each basic path. If any is invalid, then returns UNVERIFIED.
                    bool rankFuncValid = checkRankFuncValid(basicPath);
                    if (!rankFuncValid)
                    {
                        return -1;
                    }
                }

                // special case: No basic path.
                if (allBasicPaths.Count == 0)
                {
                    Expression preCondition = convertCondList2SingleCond(entry.conditions);
                    List<Expression> startConds = new List<Expression>(entry.rankingFunctions);
                    if (!checkRankFuncLowerBound(preCondition, startConds))
                    {
                        return -1;
                    }
                    ExitLocation exit = function.exitLocation;
                    Expression postCondition = convertCondList2SingleCond(exit.conditions);
                    Expression wlpExp = new ImplicationExpression(preCondition, postCondition);
                    if (solver.CheckValid(wlpExp) is not null)
                    {
                        return -1;
                    }
                }
            }
            return 1;
        }

        /* DFS to get all basic paths starting from "currloc". Called by "findAllBasicPaths". */
        public List<List<Location>> DFS(Location currLoc)
        {
            // basic paths starting from currloc in "cache".
            if (visitedLocsPathMap.ContainsKey(currLoc))
            {
                return visitedLocsPathMap[currLoc];
            }

            List<List<Location>> paths = new List<List<Location>>();

            // returns when currLoc is LoopHeadLocation or ExitLocation, except for the first time.
            if (enterTimes != 0 && (currLoc is LoopHeadLocation || currLoc is ExitLocation))
            {
                enterTimes++;
                List<Location> path = new List<Location>();
                path.Add(currLoc);
                paths.Add(path);
                if (!visitedLocsPathMap.ContainsKey(currLoc))
                {
                    visitedLocsPathMap.Add(currLoc, paths);
                }
                return paths;
            }

            enterTimes++;

            // DFS all succeeding locations.
            foreach (Location loc in currLoc.succLocations)
            {
                List<List<Location>> sub_paths = DFS(loc);
                foreach (List<Location> sub_path in sub_paths)
                {
                    List<Location> sub_path1 = new List<Location>(sub_path);
                    sub_path1.Reverse();
                    sub_path1.Add(currLoc);
                    sub_path1.Reverse();
                    paths.Add(sub_path1);
                }

                /* When encountering a FuncCallStatement, pause and add another basic path. 
                   Add succeeding location "loc" twice to signal that this is a basic path that ends with a function call.
                   There won't be any conflicts because no location contains itself in its succeeding locations. */
                if (currLoc.succStatements[currLoc.succLocations.IndexOf(loc)] is FunctionCallStatement)
                {
                    List<Location> path = new List<Location>();
                    path.Add(currLoc);
                    path.Add(loc);
                    path.Add(loc);       // signal
                    paths.Add(path);
                }
            }

            // Add to cache
            if (!visitedLocsPathMap.ContainsKey(currLoc))
            {
                visitedLocsPathMap.Add(currLoc, paths);
            }

            return paths;
        }

        /* Find all basic paths of each function.
           Parameter "entry" specifies the function's entry location. */
        public List<List<Location>> findAllBasicPaths(Location entry)
        {
            HashSet<Location> visited = new HashSet<Location>();        // visited "startLocations"
            List<List<Location>> allBasicPaths = new List<List<Location>>();
            List<List<Location>> currBasicPaths = new List<List<Location>>();
            List<Location> startLocations = new List<Location>();       // All basic paths start from "startLocations", which is implemented as a queue.
            startLocations.Add(entry);
            while (startLocations.Count != 0)
            {
                Location currStart = startLocations[0];
                startLocations.RemoveAt(0);
                if (!visited.Contains(currStart))
                {
                    visited.Add(currStart);

                    visitedLocsPathMap = new Dictionary<Location, List<List<Location>>>();
                    enterTimes = 0;
                    currBasicPaths = DFS(currStart);

                    foreach (List<Location> currBasicPath in currBasicPaths)
                    {
                        allBasicPaths.Add(currBasicPath);
                    }

                    foreach (List<Location> currBasicPath in currBasicPaths)
                    {
                        // Besides EntryLocation, only LoopHeadLocation can enter the queue.
                        if (currBasicPath[currBasicPath.Count-1] is LoopHeadLocation)
                        {
                            startLocations.Add(currBasicPath[currBasicPath.Count-1]);
                        }
                    }
                }
            }
            return allBasicPaths;
        }

        /* Given a basic path, post-condition and tail-to-head iteration starting index, find the wlp to feed into SMTSolver. */
        public Expression calculateWlp(List<Location> basicPath, Expression currCond, int startIndex)
        {
            // Iteratively calculate the wlp until the first location.
            for (int i = startIndex; i >= 0; i--)
            {
                Location loc = basicPath[i];
                Location succLoc = basicPath[i+1];
                Statement stmt = loc.succStatements[loc.succLocations.IndexOf(succLoc)];

                // assign stmt.
                if (stmt is VariableAssignStatement assignStmt)
                {
                    currCond = currCond.Substitute(assignStmt.variable, assignStmt.rhs);
                }

                // subscipt assign stmt.
                else if (stmt is SubscriptAssignStatement subscriptAssignStmt)
                {
                    Expression newArray = new ArrayUpdateExpression(new VariableExpression(subscriptAssignStmt.array),
                                                                    subscriptAssignStmt.subscript,
                                                                    subscriptAssignStmt.rhs,
                                                                    new VariableExpression(subscriptAssignStmt.array.length));
                    currCond = currCond.Substitute(subscriptAssignStmt.array, newArray);
                }

                // assume stmt.
                else if (stmt is AssumeStatement assumeStmt)
                {
                    currCond = new ImplicationExpression(assumeStmt.condition, currCond);
                }

                // assert stmt.
                else if (stmt is AssertStatement assertStmt)
                {
                    currCond = new AndExpression(assertStmt.pred, currCond);
                }

                // func call stmt, needs to substitute parameter to arguments.
                else if (stmt is FunctionCallStatement funcStmt)
                {
                    Expression funcPostCondition = convertCondList2SingleCond(funcStmt.rhs.function.exitLocation.conditions);
                    for (int j = 0; j < funcStmt.rhs.argumentVariables.Count; j++)
                    {
                        funcPostCondition = funcPostCondition.Substitute(funcStmt.rhs.function.parameters[j], new VariableExpression(funcStmt.rhs.argumentVariables[j]));
                    }
                    for (int j = 0; j < funcStmt.lhs.Count; j++)
                    {
                        funcPostCondition = funcPostCondition.Substitute(funcStmt.rhs.function.rvs[j], new VariableExpression(funcStmt.lhs[j]));
                    }
                    currCond = new ImplicationExpression(funcPostCondition, currCond);
                }
            }

            // calculate pre-condition of the basic path.
            Expression preCondition = null;
            if (basicPath[0] is EntryLocation entryLoc)
            {
                preCondition = convertCondList2SingleCond(entryLoc.conditions);
            }
            else if (basicPath[0] is LoopHeadLocation loopHeadLoc)
            {
                preCondition = convertCondList2SingleCond(loopHeadLoc.invariants);
            }

            currCond = new ImplicationExpression(preCondition, currCond);
            return currCond;
        }

        /* Ranking functions have to have lower bound 0. */
        public bool checkRankFuncLowerBound(Expression preCondition, List<Expression> startConds)
        {
            IntConstantExpression zero = new IntConstantExpression(0);
            List<Expression> rankFuncsGeZeroList = new List<Expression>();

            foreach (Expression startCond in startConds)
            {
                rankFuncsGeZeroList.Add(new GEExpression(startCond, zero));
            }

            Expression rankFuncsGeZeroExp = new ImplicationExpression(preCondition, convertCondList2SingleCond(rankFuncsGeZeroList));
            if (solver.CheckValid(rankFuncsGeZeroExp) is not null)
            {
                return false;
            }    
            return true;            
        }

        /* Check whether the ranking function is valid at the head and tail of a basic path. */
        public bool checkRankFuncValid(List<Location> basicPath)
        {
            HeadLocation startLoc = basicPath[0] as HeadLocation;
            List<Expression> startConds = new List<Expression>(startLoc.rankingFunctions);
            
            if (startConds.Count != 0)
            {
                Expression preCondition = null;
                if (basicPath[0] is EntryLocation entryLoc)
                {
                    preCondition = convertCondList2SingleCond(entryLoc.conditions);
                }
                else if (basicPath[0] is LoopHeadLocation loopHeadLoc)
                {
                    preCondition = convertCondList2SingleCond(loopHeadLoc.invariants);
                }

                // first check whether the head ranking function has a lower bound.
                if (!checkRankFuncLowerBound(preCondition, startConds))
                {
                    return false;
                }

                int startIndex = basicPath.Count-2;
                List<Expression> endConds = new List<Expression>();

                // tail ranking function: function call case.
                if (basicPath.Count >= 2 && basicPath[basicPath.Count-1] == basicPath[basicPath.Count-2])
                {
                    Location funcPredLoc = basicPath[basicPath.Count-3];
                    Location funcPostLoc = basicPath[basicPath.Count-2];
                    FunctionCallStatement stmt = funcPredLoc.succStatements[funcPredLoc.succLocations.IndexOf(funcPostLoc)] as FunctionCallStatement;
                    List<Expression> rankFuncs = new List<Expression>(stmt.rhs.function.entryLocation.rankingFunctions);
                    for (int i = 0; i < stmt.rhs.argumentVariables.Count; i++)
                    {
                        for (int j = 0; j < rankFuncs.Count; j++)
                        {
                            rankFuncs[j] = rankFuncs[j].Substitute(stmt.rhs.function.parameters[i], new VariableExpression(stmt.rhs.argumentVariables[i]));
                        }
                    }
                    endConds = rankFuncs;
                    startIndex = basicPath.Count - 4;
                }

                // tail ranking function: loop head case.
                else if (basicPath[basicPath.Count-1] is LoopHeadLocation loopHeadLoc)
                {
                    endConds = loopHeadLoc.rankingFunctions;
                }

                // only continue checking when the number of the head ranking function condition equals that of the tail ranking function condition.
                if (startConds.Count == endConds.Count)
                {
                    Dictionary<LocalVariable, LocalVariable> substituteMapping = new Dictionary<LocalVariable, LocalVariable>();
                    Dictionary<LocalVariable, LocalVariable> substituteReverseMapping = new Dictionary<LocalVariable, LocalVariable>();

                    // check the ranking function decreases according to the lexicographical order.
                    for (int i = 0; i < startConds.Count; i++)
                    {
                        HashSet<LocalVariable> substituteElements = startConds[i].GetFreeVariables();
                        foreach(LocalVariable substituteElement in substituteElements)
                        {
                            // substitute the variable at the head location to specify its value when first entering the basic path.
                            if (!substituteMapping.ContainsKey(substituteElement))
                            {
                                LocalVariable cloneSubstituteElement = new LocalVariable();
                                cloneSubstituteElement.name = "clone" + substituteElement.name;
                                cloneSubstituteElement.type = substituteElement.type;
                                substituteMapping.Add(substituteElement, cloneSubstituteElement);
                                substituteReverseMapping.Add(cloneSubstituteElement, substituteElement);
                            }
                            startConds[i] = startConds[i].Substitute(substituteElement, new VariableExpression(substituteMapping[substituteElement]));
                        }

                        Expression currCond = new LTExpression(endConds[i], startConds[i]);
                        for (int j = 0; j < i; j++)
                        {
                            currCond = new AndExpression(currCond, new EQExpression(endConds[j], startConds[j]));
                        }

                        Expression wlpToBeVerified = calculateWlp(basicPath, currCond, startIndex);

                        // substitute alias back to its original name.
                        HashSet<LocalVariable> substituteBackElements = wlpToBeVerified.GetFreeVariables();
                        foreach (LocalVariable substituteBackElement in substituteBackElements)
                        {
                            if (substituteReverseMapping.ContainsKey(substituteBackElement))
                            {
                                wlpToBeVerified = wlpToBeVerified.Substitute(substituteBackElement, new VariableExpression(substituteReverseMapping[substituteBackElement]));
                            }
                        }

                        if (solver.CheckValid(wlpToBeVerified) is null)
                        {
                            return true;
                        }
                    }
                    return false;
                }
            }
            return true;
        }

        /* Concatenate a list of conditions to a single expression using "And Expression". */
        public Expression convertCondList2SingleCond(List<Expression> condList)
        {
            Expression singleCond;
            if (condList.Count == 0)
            {
                singleCond = new BoolConstantExpression(true);
            }
            else if (condList.Count == 1)
            {
                singleCond = condList[0];
            }
            else {
                singleCond = new AndExpression(condList[0], condList[1]);
                for (int i = 2; i < condList.Count; i++)
                {
                    singleCond = new AndExpression(singleCond, condList[i]);
                }
            }
            return singleCond;
        }
    }
}