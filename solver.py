import sys
from threading import Event
from utils import SATSolverResult, load_formula, lit_to_dimacs


class Solver:
    def __init__(self, filename: str, sigkill: Event):
        self.sigkill = sigkill
        self.formula = load_formula(filename)
        self.num_vars = self.formula.num_vars
        num_lits = self.formula.num_lits

        # Присваивание: values[ℓ] = 1 (истинен), -1 (ложен), 0 (не означен).
        # Хранится и для ℓ, и для ¬ℓ: values[ℓ] == -values[ℓ ^ 1].
        self.values = [0] * num_lits

        # Трейл — означенные литералы в порядке присваивания.
        # trail[:propagated] уже распространены, trail[propagated:] — ещё нет.
        self.trail = []
        self.propagated = 0

        # control[i] — позиция в trail решения уровня i + 1;
        # текущий уровень решения = len(control).
        self.control = []

        self.model = None

        self.preprocess()

    def preprocess(self):
        """
        Разбор дизъюнктов формулы:
          clauses          — дизъюнкты длины ≥ 2, без повторов литералов и тавтологий (a ∨ ¬a ∨ ...)
          units            — литералы единичных дизъюнктов
          has_empty_clause — во входе есть пустой дизъюнкт (формула невыполнима)
        """
        self.clauses = []
        self.units = []
        self.has_empty_clause = False
        for clause in self.formula.clauses:
            lits = set(clause)
            if not lits:
                self.has_empty_clause = True
            elif any(lit ^ 1 in lits for lit in lits):
                continue
            elif len(lits) == 1:
                self.units.append(lits.pop())
            else:
                self.clauses.append(list(lits))

    def level(self) -> int:
        return len(self.control)

    def assign(self, lit: int) -> bool:
        """Сделать ℓ истинным на текущем уровне."""
        if self.values[lit] > 0:
            return True
        if self.values[lit] < 0:
            return False
        self.values[lit] = 1
        self.values[lit ^ 1] = -1
        self.trail.append(lit)
        return True

    def decide(self, lit: int):
        """Открыть новый уровень решения и сделать ℓ истинным."""
        self.control.append(len(self.trail))
        self.assign(lit)

    def decision(self, level: int) -> int:
        """Литерал-решение уровня level (1 ≤ level ≤ self.level())."""
        return self.trail[self.control[level - 1]]

    def backtrack(self, level: int):
        """Отменить все присваивания уровней > level."""
        if level >= len(self.control):
            return
        values, trail = self.values, self.trail
        start = self.control[level]
        for i in range(start, len(trail)):
            lit = trail[i]
            values[lit] = 0
            values[lit ^ 1] = 0
        del trail[start:]
        del self.control[level:]
        self.propagated = start

    def save_model(self):
        values = self.values
        self.model = [lit_to_dimacs(2 * v if values[2 * v] > 0 else 2 * v + 1)
                      for v in range(1, self.num_vars + 1)]

    def build_occurrences(self):
        self.occurrences = [[] for _ in range(self.formula.num_lits)]
        for c in self.clauses:
            for lit in c:
                self.occurrences[lit].append(c)

    def build_watches(self):
        num_lits = self.formula.num_lits
        self.binary = [[] for _ in range(num_lits)]
        self.watches = [[] for _ in range(num_lits)]
        scores = [0.0] * num_lits
        for c in self.clauses:
            weight = 2.0 ** -len(c)
            for lit in c:
                scores[lit] += weight
            if len(c) == 2:
                self.binary[c[0]].append(c[1])
                self.binary[c[1]].append(c[0])
            else:
                self.watches[c[0]].append([c[1], c])
                self.watches[c[1]].append([c[0], c])

        self.literal_order = sorted(
            range(1, self.num_vars + 1),
            key=lambda v: scores[2 * v] + scores[2 * v + 1],
            reverse=True,
        )
        self.preferred_literal = [0] * (self.num_vars + 1)
        for v in range(1, self.num_vars + 1):
            positive = 2 * v
            negative = positive + 1
            self.preferred_literal[v] = (
                positive if scores[positive] >= scores[negative] else negative
            )

    class Interrupted(Exception):
        pass

    def propagate(self) -> bool:
        """
        UnitPropagate: распространить литералы trail[propagated:].
        Возвращает True, если найден конфликт (все литералы дизъюнкта ложны).
        """
        while self.propagated < len(self.trail):
            if self.sigkill.is_set():
                raise self.Interrupted()

            p = self.trail[self.propagated]
            self.propagated += 1
            false_lit = p ^ 1

            for other in self.binary[false_lit]:
                v = self.values[other]
                if v == 1:
                    continue
                if v == -1:
                    return True
                if not self.assign(other):
                    return True

            ws = self.watches[false_lit]
            i = 0
            while i < len(ws):
                blocker, clause = ws[i]
                if self.values[blocker] == 1:
                    i += 1
                    continue

                if clause[0] == false_lit:
                    clause[0], clause[1] = clause[1], clause[0]
                other = clause[0]
                if self.values[other] == 1:
                    ws[i][0] = other
                    i += 1
                    continue

                replacement = 0
                for k in range(2, len(clause)):
                    if self.values[clause[k]] != -1:
                        replacement = k
                        break

                if replacement:
                    clause[1], clause[replacement] = (
                        clause[replacement], clause[1]
                    )
                    ws[i] = ws[-1]
                    ws.pop()
                    self.watches[clause[1]].append([other, clause])
                    continue

                ws[i][0] = other
                if self.values[other] == -1:
                    return True
                if not self.assign(other):
                    return True
                i += 1

        return False

    def choose_literal(self):
        """
        ChooseLiteral: литерал для следующего решения или None, если все
        переменные означены.
        """
        for v in self.literal_order:
            if self.values[2 * v] == 0:
                return self.preferred_literal[v]
        return None

    def dpll_(self) -> bool:
        while True:
            if self.sigkill.is_set():
                raise self.Interrupted()

            if self.propagate():
                if self.level() == 0:
                    return False
                L = self.level()
                last_lit = self.decision(L)
                self.backtrack(L - 1)
                if not self.assign(last_lit ^ 1):
                    continue
                continue

            lit = self.choose_literal()
            if lit is None:
                return True

            self.decide(lit)

    def solve(self) -> SATSolverResult:
        if self.sigkill.is_set():  # TODO: your code should check this predicate frequently! If it is set, you should return
            return SATSolverResult.UNKNOWN

        if self.has_empty_clause:
            return SATSolverResult.UNSAT

        self.build_watches()

        for u in self.units:
            if self.sigkill.is_set():
                return SATSolverResult.UNKNOWN
            if not self.assign(u):
                return SATSolverResult.UNSAT

        try:
            sat = self.dpll_()
        except self.Interrupted:
            return SATSolverResult.UNKNOWN

        if sat:
            self.save_model()
            return SATSolverResult.SAT

        return SATSolverResult.UNSAT


# comment for CI
if __name__ == "__main__":
    result = Solver(sys.argv[1], Event()).solve()
    if result == SATSolverResult.SAT:
        print("sat")
    elif result == SATSolverResult.UNSAT:
        print("unsat")
    else:
        print("unknown")
