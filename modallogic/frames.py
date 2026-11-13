"""Composable Kripke frame classes and accessibility relation property mixins."""

from typing import Set, Tuple, Dict, Any, Iterable, Optional, List, Type
from .semantics import KripkeFrame


class FrameProperty:
    """Standard relational accessibility properties."""

    REFLEXIVE = "reflexive"
    TRANSITIVE = "transitive"
    SYMMETRIC = "symmetric"
    SERIAL = "serial"
    EUCLIDEAN = "euclidean"
    CONFLUENT = "confluent"
    DIRECTED = "directed"
    WELL_FOUNDED = "well_founded"
    CONVERSE_WELL_FOUNDED = "converse_well_founded"


class ReflexiveFrameMixin:
    """Mixin enforcing reflexivity: forall w, w R w."""

    REQUIRED_PROPERTIES = (FrameProperty.REFLEXIVE,)

    def check_reflexive_property(self: KripkeFrame) -> Tuple[bool, Optional[Any]]:
        for w in sorted(list(self.worlds), key=lambda x: str(x)):
            if (w, w) not in self.relation:
                return False, w
        return True, None


class TransitiveFrameMixin:
    """Mixin enforcing transitivity: forall w, u, v, (w R u and u R v) implies w R v."""

    REQUIRED_PROPERTIES = (FrameProperty.TRANSITIVE,)

    def check_transitive_property(self: KripkeFrame) -> Tuple[bool, Optional[Tuple[Any, Any, Any]]]:
        for w, u in sorted(list(self.relation), key=lambda p: (str(p[0]), str(p[1]))):
            for v in sorted(list(self.successors(u)), key=lambda x: str(x)):
                if (w, v) not in self.relation:
                    return False, (w, u, v)
        return True, None


class SymmetricFrameMixin:
    """Mixin enforcing symmetry: forall w, u, w R u implies u R w."""

    REQUIRED_PROPERTIES = (FrameProperty.SYMMETRIC,)

    def check_symmetric_property(self: KripkeFrame) -> Tuple[bool, Optional[Tuple[Any, Any]]]:
        for w, u in sorted(list(self.relation), key=lambda p: (str(p[0]), str(p[1]))):
            if (u, w) not in self.relation:
                return False, (w, u)
        return True, None


class SerialFrameMixin:
    """Mixin enforcing seriality: forall w, exists u such that w R u."""

    REQUIRED_PROPERTIES = (FrameProperty.SERIAL,)

    def check_serial_property(self: KripkeFrame) -> Tuple[bool, Optional[Any]]:
        for w in sorted(list(self.worlds), key=lambda x: str(x)):
            if not self.successors(w):
                return False, w
        return True, None


class EuclideanFrameMixin:
    """Mixin enforcing euclideanness: forall w, u, v, (w R u and w R v) implies u R v."""

    REQUIRED_PROPERTIES = (FrameProperty.EUCLIDEAN,)

    def check_euclidean_property(self: KripkeFrame) -> Tuple[bool, Optional[Tuple[Any, Any, Any]]]:
        for w in sorted(list(self.worlds), key=lambda x: str(x)):
            succ = sorted(list(self.successors(w)), key=lambda x: str(x))
            for u in succ:
                for v in succ:
                    if (u, v) not in self.relation:
                        return False, (w, u, v)
        return True, None


class ConfluentFrameMixin:
    """Mixin enforcing Church-Rosser confluence (directedness):
    forall w, u, v, (w R u and w R v) implies exists z: (u R z and v R z).
    """

    REQUIRED_PROPERTIES = (FrameProperty.CONFLUENT,)

    def check_confluent_property(self: KripkeFrame) -> Tuple[bool, Optional[Tuple[Any, Any, Any]]]:
        for w in sorted(list(self.worlds), key=lambda x: str(x)):
            succ = sorted(list(self.successors(w)), key=lambda x: str(x))
            for i, u in enumerate(succ):
                succ_u = self.successors(u)
                for v in succ[i:]:
                    succ_v = self.successors(v)
                    if not (succ_u & succ_v):
                        return False, (w, u, v)
        return True, None


# DirectedFrameMixin is an alias for ConfluentFrameMixin
class DirectedFrameMixin(ConfluentFrameMixin):
    """Alias mixin for directedness."""

    REQUIRED_PROPERTIES = (FrameProperty.DIRECTED,)


class ConverseWellFoundedFrameMixin:
    """Mixin enforcing converse well-foundedness (no directed cycles on finite frames)."""

    REQUIRED_PROPERTIES = (FrameProperty.CONVERSE_WELL_FOUNDED,)

    def check_converse_well_founded_property(self: KripkeFrame) -> Tuple[bool, Optional[List[Any]]]:
        visited: Set[Any] = set()
        in_stack: Set[Any] = set()
        path: List[Any] = []

        def _dfs(node: Any) -> Optional[List[Any]]:
            visited.add(node)
            in_stack.add(node)
            path.append(node)
            for succ in sorted(list(self.successors(node)), key=lambda x: str(x)):
                if succ in in_stack:
                    idx = path.index(succ)
                    return path[idx:] + [succ]
                if succ not in visited:
                    cycle = _dfs(succ)
                    if cycle is not None:
                        return cycle
            path.pop()
            in_stack.remove(node)
            return None

        for w in sorted(list(self.worlds), key=lambda x: str(x)):
            if w not in visited:
                cycle = _dfs(w)
                if cycle is not None:
                    return False, cycle
        return True, None


class WellFoundedFrameMixin:
    """Mixin enforcing well-foundedness (no descending cycles on finite frames)."""

    REQUIRED_PROPERTIES = (FrameProperty.WELL_FOUNDED,)

    def check_well_founded_property(self: KripkeFrame) -> Tuple[bool, Optional[List[Any]]]:
        # A finite relation has no infinite descending chains iff it has no cycles
        visited: Set[Any] = set()
        in_stack: Set[Any] = set()
        path: List[Any] = []

        def _dfs_pred(node: Any) -> Optional[List[Any]]:
            visited.add(node)
            in_stack.add(node)
            path.append(node)
            for pred in sorted(list(self.predecessors(node)), key=lambda x: str(x)):
                if pred in in_stack:
                    idx = path.index(pred)
                    return path[idx:] + [pred]
                if pred not in visited:
                    cycle = _dfs_pred(pred)
                    if cycle is not None:
                        return cycle
            path.pop()
            in_stack.remove(node)
            return None

        for w in sorted(list(self.worlds), key=lambda x: str(x)):
            if w not in visited:
                cycle = _dfs_pred(w)
                if cycle is not None:
                    return False, cycle
        return True, None


class ComposableFrame(KripkeFrame):
    """Base class for composable frames with automated property validation."""

    SYSTEM_NAME = "Base"
    EXPECTED_PROPERTIES: Tuple[str, ...] = ()

    def __init__(
        self,
        worlds: Iterable[Any],
        relation: Iterable[Tuple[Any, Any]],
        valuation: Optional[Dict[str, Iterable[Any]]] = None,
        validate: bool = False,
    ):
        super().__init__(worlds, relation, valuation)
        if validate:
            self.validate()

    def validation_report(self) -> Dict[str, Any]:
        """Audit all expected relational properties against this frame instance."""
        report: Dict[str, Any] = {
            "system": self.SYSTEM_NAME,
            "is_valid": True,
            "satisfied": [],
            "failures": {},
        }

        for prop in self.EXPECTED_PROPERTIES:
            sat, witness = self._check_single_property(prop)
            if sat:
                report["satisfied"].append(prop)
            else:
                report["is_valid"] = False
                report["failures"][prop] = witness

        return report

    def _check_single_property(self, prop: str) -> Tuple[bool, Any]:
        if prop == FrameProperty.REFLEXIVE:
            return self.is_reflexive(), None if self.is_reflexive() else self._witness_non_reflexive()
        if prop == FrameProperty.TRANSITIVE:
            return self.is_transitive(), None if self.is_transitive() else self._witness_non_transitive()
        if prop == FrameProperty.SYMMETRIC:
            return self.is_symmetric(), None if self.is_symmetric() else self._witness_non_symmetric()
        if prop == FrameProperty.SERIAL:
            return self.is_serial(), None if self.is_serial() else self._witness_non_serial()
        if prop == FrameProperty.EUCLIDEAN:
            return self.is_euclidean(), None if self.is_euclidean() else self._witness_non_euclidean()
        if prop in (FrameProperty.CONFLUENT, FrameProperty.DIRECTED):
            return self.is_confluent(), None if self.is_confluent() else self._witness_non_confluent()
        if prop == FrameProperty.CONVERSE_WELL_FOUNDED:
            return self.is_converse_well_founded(), None if self.is_converse_well_founded() else self._witness_cycle()
        if prop == FrameProperty.WELL_FOUNDED:
            return self.is_converse_well_founded(), None if self.is_converse_well_founded() else self._witness_cycle()
        raise ValueError(f"Unknown frame property: {prop}")

    def _witness_non_reflexive(self) -> Optional[Any]:
        for w in sorted(list(self.worlds), key=lambda x: str(x)):
            if (w, w) not in self.relation:
                return w
        return None

    def _witness_non_transitive(self) -> Optional[Tuple[Any, Any, Any]]:
        for w, u in sorted(list(self.relation), key=lambda p: (str(p[0]), str(p[1]))):
            for v in sorted(list(self.successors(u)), key=lambda x: str(x)):
                if (w, v) not in self.relation:
                    return (w, u, v)
        return None

    def _witness_non_symmetric(self) -> Optional[Tuple[Any, Any]]:
        for w, u in sorted(list(self.relation), key=lambda p: (str(p[0]), str(p[1]))):
            if (u, w) not in self.relation:
                return (w, u)
        return None

    def _witness_non_serial(self) -> Optional[Any]:
        for w in sorted(list(self.worlds), key=lambda x: str(x)):
            if not self.successors(w):
                return w
        return None

    def _witness_non_euclidean(self) -> Optional[Tuple[Any, Any, Any]]:
        for w in sorted(list(self.worlds), key=lambda x: str(x)):
            succ = sorted(list(self.successors(w)), key=lambda x: str(x))
            for u in succ:
                for v in succ:
                    if (u, v) not in self.relation:
                        return (w, u, v)
        return None

    def _witness_non_confluent(self) -> Optional[Tuple[Any, Any, Any]]:
        for w in sorted(list(self.worlds), key=lambda x: str(x)):
            succ = sorted(list(self.successors(w)), key=lambda x: str(x))
            for i, u in enumerate(succ):
                succ_u = self.successors(u)
                for v in succ[i:]:
                    succ_v = self.successors(v)
                    if not (succ_u & succ_v):
                        return (w, u, v)
        return None

    def _witness_cycle(self) -> Optional[List[Any]]:
        visited: Set[Any] = set()
        in_stack: Set[Any] = set()
        path: List[Any] = []

        def _dfs(node: Any) -> Optional[List[Any]]:
            visited.add(node)
            in_stack.add(node)
            path.append(node)
            for succ in sorted(list(self.successors(node)), key=lambda x: str(x)):
                if succ in in_stack:
                    idx = path.index(succ)
                    return path[idx:] + [succ]
                if succ not in visited:
                    cycle = _dfs(succ)
                    if cycle is not None:
                        return cycle
            path.pop()
            in_stack.remove(node)
            return None

        for w in sorted(list(self.worlds), key=lambda x: str(x)):
            if w not in visited:
                c = _dfs(w)
                if c is not None:
                    return c
        return None

    def is_valid_frame(self) -> bool:
        """Return True if frame satisfies all expected properties for this class."""
        return self.validation_report()["is_valid"]

    def validate(self) -> None:
        """Validate expected properties, raising ValueError on failure."""
        report = self.validation_report()
        if not report["is_valid"]:
            failures = report["failures"]
            raise ValueError(
                f"Frame is not a valid {self.SYSTEM_NAME} frame. Violations: {failures}"
            )


# Concrete Composable Modal Frame Classes


class KFrame(ComposableFrame):
    """Basic normal modal frame K with no relational restrictions."""

    SYSTEM_NAME = "K"
    EXPECTED_PROPERTIES = ()


class KDFrame(SerialFrameMixin, ComposableFrame):
    """Deontic modal frame KD (serial relation)."""

    SYSTEM_NAME = "KD"
    EXPECTED_PROPERTIES = (FrameProperty.SERIAL,)


class TFrame(ReflexiveFrameMixin, ComposableFrame):
    """Reflexive modal frame T / KT."""

    SYSTEM_NAME = "T"
    EXPECTED_PROPERTIES = (FrameProperty.REFLEXIVE,)


KTFrame = TFrame


class KBFrame(SymmetricFrameMixin, ComposableFrame):
    """Brouwerian modal frame KB (symmetric relation)."""

    SYSTEM_NAME = "KB"
    EXPECTED_PROPERTIES = (FrameProperty.SYMMETRIC,)


class K4Frame(TransitiveFrameMixin, ComposableFrame):
    """Transitive modal frame K4."""

    SYSTEM_NAME = "K4"
    EXPECTED_PROPERTIES = (FrameProperty.TRANSITIVE,)


class K45Frame(TransitiveFrameMixin, EuclideanFrameMixin, ComposableFrame):
    """Transitive and euclidean modal frame K45."""

    SYSTEM_NAME = "K45"
    EXPECTED_PROPERTIES = (FrameProperty.TRANSITIVE, FrameProperty.EUCLIDEAN)


class KD45Frame(SerialFrameMixin, TransitiveFrameMixin, EuclideanFrameMixin, ComposableFrame):
    """Doxastic modal frame KD45 (serial, transitive, euclidean relation)."""

    SYSTEM_NAME = "KD45"
    EXPECTED_PROPERTIES = (
        FrameProperty.SERIAL,
        FrameProperty.TRANSITIVE,
        FrameProperty.EUCLIDEAN,
    )


class S4Frame(ReflexiveFrameMixin, TransitiveFrameMixin, ComposableFrame):
    """Preorder modal frame S4 (reflexive and transitive relation)."""

    SYSTEM_NAME = "S4"
    EXPECTED_PROPERTIES = (FrameProperty.REFLEXIVE, FrameProperty.TRANSITIVE)


class S5Frame(
    ReflexiveFrameMixin,
    TransitiveFrameMixin,
    SymmetricFrameMixin,
    EuclideanFrameMixin,
    ComposableFrame,
):
    """Equivalence modal frame S5 (reflexive, symmetric, transitive, and euclidean relation)."""

    SYSTEM_NAME = "S5"
    EXPECTED_PROPERTIES = (
        FrameProperty.REFLEXIVE,
        FrameProperty.TRANSITIVE,
        FrameProperty.SYMMETRIC,
        FrameProperty.EUCLIDEAN,
    )


class GLFrame(TransitiveFrameMixin, ConverseWellFoundedFrameMixin, ComposableFrame):
    """Gödel-Löb provability frame GL (transitive and converse well-founded relation)."""

    SYSTEM_NAME = "GL"
    EXPECTED_PROPERTIES = (
        FrameProperty.TRANSITIVE,
        FrameProperty.CONVERSE_WELL_FOUNDED,
    )


class ConfluentFrame(ConfluentFrameMixin, ComposableFrame):
    """Confluent / directed modal frame (Church-Rosser condition)."""

    SYSTEM_NAME = "Confluent"
    EXPECTED_PROPERTIES = (FrameProperty.CONFLUENT,)


DirectedFrame = ConfluentFrame


FRAME_CLASSES: Dict[str, Type[ComposableFrame]] = {
    "K": KFrame,
    "KD": KDFrame,
    "T": TFrame,
    "KT": KTFrame,
    "KB": KBFrame,
    "K4": K4Frame,
    "K45": K45Frame,
    "KD45": KD45Frame,
    "S4": S4Frame,
    "S5": S5Frame,
    "GL": GLFrame,
    "C4": ConfluentFrame,
    "CONFLUENT": ConfluentFrame,
    "DIRECTED": DirectedFrame,
}


def create_frame(
    system_name: str,
    worlds: Iterable[Any],
    relation: Iterable[Tuple[Any, Any]],
    valuation: Optional[Dict[str, Iterable[Any]]] = None,
    validate: bool = False,
) -> ComposableFrame:
    """Instantiate the appropriate composable frame class for the designated modal system."""
    key = system_name.upper()
    if key not in FRAME_CLASSES:
        raise ValueError(
            f"Unsupported modal frame system: {system_name}. "
            f"Available systems: {list(FRAME_CLASSES.keys())}"
        )
    cls = FRAME_CLASSES[key]
    return cls(worlds, relation, valuation, validate=validate)
