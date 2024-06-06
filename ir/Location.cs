using System.IO;

using System.Collections.Generic;

using System.Diagnostics;
using System.Diagnostics.Contracts;

namespace cminor
{
    /// <summary> 用于表示“程序位置”的类。 </summary>
    /// FIXME: 目前对 location 的处理有问题，EntryLocation 可能同时是 ExitLocation 和 LoopHeadLocation，在类型设计和生成 CFA 的时候都需要改。
    class Location
    {
        public List<Location> predLocations = new List<Location>();

        // 下面这俩的大小得一致
        public List<Location> succLocations = new List<Location>();
        // 边上也可以没有 statement
        public List<Statement?> succStatements = new List<Statement?>();

        public Location() { }

        public Location(Function currentFunction)
        {
            currentFunction.locations.Add(this);
        }

        public Location(Function currentFunction, Location lastLocation, Statement? statement = null)
        {
            predLocations.Add(lastLocation);

            lastLocation.succLocations.Add(this);
            lastLocation.succStatements.Add(statement);

            currentFunction.locations.Add(this);
        }

        public bool RemovePred(Location v) {
            return predLocations.Remove(v);
        }

        public bool RemoveSucc(Location v) {
            int i = succLocations.IndexOf(v);
            if (i != -1) {
                succLocations.RemoveAt(i);
                succStatements.RemoveAt(i);
                return true;
            } else {
                return false;
            }
        }

        public static void AddEdge(Location u, Location v, Statement statement)
        {
            u.succLocations.Add(v);
            u.succStatements.Add(statement);

            v.predLocations.Add(u);
        }

        // 将 v 并入 u
        public static Location Merge(Function currentFunction, Location u, Location v)
        {
            // 在函数的位置列表中删除 v
            currentFunction.locations.Remove(v);

            // 在 v 的前驱和后继里删掉 u
            v.RemovePred(u);
            v.RemoveSucc(u);
            u.RemovePred(u);
            u.RemoveSucc(v);

            // 对于 v 的前驱，把它相应的后继改为 u
            foreach (Location pred in v.predLocations)
                for (int i = 0; i < pred.succLocations.Count; ++i)
                    if (pred.succLocations[i] == v)
                        pred.succLocations[i] = u;
            // 对于 v 的后继，把它相应的前驱改为 u
            foreach (Location succ in v.succLocations)
                for (int i = 0; i < succ.predLocations.Count; ++i)
                    if (succ.predLocations[i] == v)
                        succ.predLocations[i] = u;

            // 合并 u 和 v 的前驱和后继
            foreach (Location pred in v.predLocations)
                if (!u.predLocations.Contains(pred))
                    u.predLocations.Add(pred);
            u.succLocations.AddRange(v.succLocations);
            u.succStatements.AddRange(v.succStatements);

            return u;
        }
        
        protected void PrintPredecessors(TextWriter writer)
        {
            writer.Write("\tpredecessors:");
            foreach (Location pred in predLocations)
                writer.Write(" " + pred);
            writer.WriteLine();
        }
        protected void PrintSuccessors(TextWriter writer)
        {
            writer.Write("\tsuccessors:\n");
            for (int i = 0; i < succLocations.Count; ++i)
            {
                writer.Write("\t\t" + succLocations[i] + " ");
                if (succStatements[i] is not null) {
                    succStatements[i].Print(writer);
                } else {
                    writer.WriteLine("");
                }
            }
        }
        protected void PrintCondition(TextWriter writer, string name, Expression condition)
        {
            writer.Write($"\t{name} ");
            condition.Print(writer);
            writer.Write("\n");
        }

        public virtual void Print(TextWriter writer)
        {
            writer.WriteLine(this + ":");

            PrintPredecessors(writer);
            PrintSuccessors(writer);
        }

        static int numberCounter = 0;
        public int number { get; } = ++numberCounter;

        public override string ToString() => $"_LOC#{number}";
    }

    sealed class ExitLocation : Location
    {
        public List<Expression> conditions = new List<Expression>();

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(succLocations.Count == 0);
            Contract.Invariant(succStatements.Count == 0);
            foreach (Expression cond in conditions)
                Contract.Invariant(cond.type is BoolType);
        }

        public override void Print(TextWriter writer)
        {
            writer.WriteLine(this + ":");

            PrintPredecessors(writer);

            foreach (Expression condition in conditions)
                PrintCondition(writer, "ensures", condition);
        }

        public override string ToString() => $"_EXIT_LOC#{number}";
    }

    /// <summary> 用于表示“头”（循环头以及函数头）的程序位置的抽象类。 </summary>
    abstract class HeadLocation : Location
    {
        public List<Expression> rankingFunctions = new List<Expression>();

        public HeadLocation() { }

        public HeadLocation(Function currentFunction, Location lastLocation)
            : base(currentFunction, lastLocation) { }

        abstract protected void PrintRankingFunction(TextWriter writer);
    }

    /// <summary> 前置条件块，或者说函数头块，里面包括前置条件和秩函数。 </summary>
    sealed class EntryLocation : HeadLocation
    {
        public List<Expression> conditions = new List<Expression>();

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            Contract.Invariant(predLocations.Count == 0);
            foreach (Expression cond in conditions)
                Contract.Invariant(cond.type is BoolType);
        }

        public override void Print(TextWriter writer)
        {
            writer.WriteLine(this + ":");

            PrintSuccessors(writer);

            foreach (Expression cond in conditions)
                PrintCondition(writer, "requires", cond);

            PrintRankingFunction(writer);
        }

        protected override void PrintRankingFunction(TextWriter writer)
        {
            writer.WriteLine("\tdecreases (");
            foreach (Expression rankingFunction in rankingFunctions)
            {
                writer.Write("\t");
                rankingFunction.Print(writer);
                writer.WriteLine("");
            }
            writer.WriteLine("\t)");
        }

        public override string ToString() => $"_ENTRY_LOC#{number}";
    }

    /// <summary> 循环头位置，其中包括循环不变式和秩函数。 </summary>
    sealed class LoopHeadLocation : HeadLocation
    {
        // 这里的 statements 是用来算 condition 的！

        public List<Expression> invariants = new List<Expression>();

        public LoopHeadLocation(Function currentFunction, Location lastLocation)
            : base(currentFunction, lastLocation) { }

        [ContractInvariantMethod]
        void ObjectInvariant()
        {
            foreach (Expression cond in invariants)
                Contract.Invariant(cond.type is BoolType);
        }

        public override void Print(TextWriter writer)
        {
            writer.WriteLine(this + ":");

            PrintPredecessors(writer);
            PrintSuccessors(writer);

            foreach (Expression invariant in invariants)
                PrintCondition(writer, "loop invariant", invariant);

            PrintRankingFunction(writer);
        }

        protected override void PrintRankingFunction(TextWriter writer)
        {
            writer.WriteLine("\tloop variant (");
            foreach (Expression rankingFunction in rankingFunctions)
            {
                writer.Write("\t");
                rankingFunction.Print(writer);
                writer.WriteLine("");
            }
            writer.WriteLine("\t)");
        }

        public override string ToString() => $"_LOOPHEAD_LOC#{number}";
    }
}
