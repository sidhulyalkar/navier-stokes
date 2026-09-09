from __future__ import annotations

from .models import EvidenceLevel, Mechanism, ResidualAtom, SourceAnchor


def _s(section: str, page: int, statement: str, lean_file: str | None = None,
       lean_declaration: str | None = None) -> SourceAnchor:
    return SourceAnchor(section, page, statement, lean_file, lean_declaration)


def residual_atoms() -> list[ResidualAtom]:
    """Machine-readable atlas of the proof architecture.

    This is a structural atlas extracted from the published proof.  It is not a
    transcription of every term in the analytic residual and does not claim an
    additive decomposition of the final force.
    """
    return [
        ResidualAtom(
            "S4_SIMILARITY_CORE", "leading-base", "inner-core", "momentum",
            "similarity_profile", "Sets the anisotropic concentrating background and leading balances.",
            _s("4", 24, "Construct leading axisymmetric profiles in similarity variables.",
               "NavierStokes/ConstructedSlowBase.lean"),
            forcing_exposure="indirect", if_removed="No reference singular background remains.",
        ),
        ResidualAtom(
            "S4_ANNULAR_STRESS", "leading-base", "annulus", "tangential-momentum",
            "annular_stress", "Encodes the singular tangential background residual as minus cylindrical stress divergence.",
            _s("4", 24, "Leading tangential residual is represented by divergence of a two-component stress.",
               "NavierStokes/ActualBaseResidual.lean"),
            dependencies=("S4_SIMILARITY_CORE",), cancellation_partner=("S7_COVARIANCE_REALIZATION",),
            forcing_exposure="high if uncancelled", if_removed="Requires redesign of the base profile or another internal stress source.",
        ),
        ResidualAtom(
            "S4_HEAT_EXTERIOR", "leading-base", "exterior", "azimuthal-momentum",
            "heat_exterior", "Provides an exact exterior with zero local Navier-Stokes residual.",
            _s("4 / App. A", 24, "Profiles match to an exact radial heat exterior.",
               "NavierStokes/ConstructedSlowBase.lean"),
            dependencies=("S4_SIMILARITY_CORE",), forcing_exposure="reduces localization burden",
            if_removed="Need a different global/exterior matching construction.",
        ),
        ResidualAtom(
            "S5_HIGHER_BASE", "background-correction", "core+annulus", "all-momentum",
            "higher_order_base", "Corrects axial viscosity and remaining radial terms order-by-order while preserving divergence and exterior.",
            _s("5", 45, "Axisymmetric corrections create the smooth background and annular physical stress.",
               "NavierStokes/BaseResidual.lean"),
            dependencies=("S4_SIMILARITY_CORE", "S4_ANNULAR_STRESS"), cancellation_partner=("S9_FLAT_SUM",),
            forcing_exposure="prevents singular residual", if_removed="Uncancelled higher-order residual terms remain.",
        ),
        ResidualAtom(
            "S5_FLAT_BASE_ERROR", "background-correction", "profile-box", "momentum",
            "flat_base_error", "Leaves a remainder flat to every algebraic order after subtracting annular stress divergence.",
            _s("5.5", 60, "Proposition 5.5: R(u_B,p_B) = -div_cyl T_phys + E_B with E_B flat.",
               "NavierStokes/ActualBaseResidual.lean"),
            dependencies=("S5_HIGHER_BASE",), forcing_exposure="flat remainder",
            if_removed="Current proof loses all-order control of the background residual.",
        ),
        ResidualAtom(
            "S6_SUPPORT_SEPARATION", "wave-geometry", "auxiliary-torus", "oscillatory",
            "support_separation", "Separates labels so distinct wave packets do not generate uncontrolled cross terms.",
            _s("6", 62, "Auxiliary torus and separated oscillatory supports."),
            dependencies=("S5_HIGHER_BASE",), forcing_exposure="none",
            if_removed="Cross-label quadratic interactions require a new closure argument.",
        ),
        ResidualAtom(
            "S7_PULSE_SEED", "wave-realization", "annulus", "oscillatory",
            "pulse_seeding", "The leading pulse solves a homogeneous zero-source amplitude equation with specified nonzero pulse-interval initial amplitude; temporal localization in exponentially small tails turns this into a globally supported construction and contributes the physical seed residual.",
            _s("2.2 / 7.2", 77, "Leading covariance uses a zero-source homogeneous pulse with specified nonzero initial amplitude; temporal cutoff acts in exponentially small tails."),
            dependencies=("S6_SUPPORT_SEPARATION",), forcing_exposure="direct",
            if_removed="Zero-source linear evolution from zero pulse data stays zero; replace with initial-data or endogenous seeding.",
        ),
        ResidualAtom(
            "S7_AMPLIFY_DAMP", "wave-realization", "annulus", "oscillatory",
            "amplify_then_damp", "Uses background shear for growth and wavenumber compression plus viscosity for later decay.",
            _s("7", 73, "Homogeneous pulse grows and decays under background shear and viscosity.",
               "NavierStokes/LinearWaveBounds.lean"),
            dependencies=("S7_PULSE_SEED",), forcing_exposure="none after seed",
            if_removed="No controlled pulse lifecycle to realize stress with flat tails.",
        ),
        ResidualAtom(
            "S7_COVARIANCE_REALIZATION", "wave-realization", "annulus", "mean tangential stress",
            "stress_cone", "Chooses positive squared amplitudes of two wave families so averaged quadratic flux realizes the leading annular stress.",
            _s("7.3", 82, "Proposition 7.5 realizes the target stress inside a strict positive covariance cone.",
               "NavierStokes/ActivationCone.lean"),
            dependencies=("S4_ANNULAR_STRESS", "S7_AMPLIFY_DAMP"), cancellation_partner=("S4_ANNULAR_STRESS",),
            forcing_exposure="removes singular forcing need", if_removed="The singular annular stress divergence reappears unless base geometry changes.",
        ),
        ResidualAtom(
            "S7_CURL_CORRECTION", "wave-realization", "annulus", "divergence",
            "curl_realization", "Takes curls of supported vector potentials to enforce exact incompressibility, creating controlled correction errors.",
            _s("7", 73, "Lemma 7.7 enforces exact incompressibility by curl."),
            dependencies=("S7_COVARIANCE_REALIZATION",), forcing_exposure="none",
            if_removed="Velocity correction is not certified divergence-free.",
        ),
        ResidualAtom(
            "S8_MEAN_CORRECTION", "mean-correction", "annulus", "zero-harmonic momentum",
            "mean_corrections", "Removes zero auxiliary-average residual and updates compactly supported mean fields.",
            _s("8", 88, "Compactly supported mean corrections."),
            dependencies=("S7_CURL_CORRECTION",), forcing_exposure="prevents residual leakage",
            if_removed="Zero-harmonic residual defects persist.",
        ),
        ResidualAtom(
            "S8_MOMENT_REPAIR", "mean-correction", "annulus", "radial moments",
            "moment_repair", "Repairs compact-support defects while preserving two moment constraints required for exterior matching.",
            _s("8", 88, "Five-equation mean system corrects three defects while preserving two moment constraints."),
            dependencies=("S8_MEAN_CORRECTION", "S4_HEAT_EXTERIOR"), forcing_exposure="prevents localization/exterior defects",
            if_removed="Mean correction may break support or exterior matching constraints.",
        ),
        ResidualAtom(
            "S9_CORRECTION_CYCLE", "residual-improvement", "all-local", "all-residual",
            "correction_cycle", "Recomputes the full nonlinear residual and improves decay order by a fixed positive power each cycle.",
            _s("9.3", 107, "Proposition 9.6 increments residual exponents by 1/10.",
               "NavierStokes/ActualCycleResidualBounds.lean"),
            dependencies=("S8_MOMENT_REPAIR",), forcing_exposure="drives residual toward flatness",
            if_removed="Finite-stage errors remain singular/non-flat.",
        ),
        ResidualAtom(
            "S9_FLAT_SUM", "residual-improvement", "local-domain", "all-residual",
            "flat_summation", "Sums finite corrections with shrinking cutoffs so every physical residual jet vanishes to every order at the singularity.",
            _s("9.5", 114, "Proposition 9.9 produces the local field with all conclusions including residual flatness.",
               "NavierStokes/DiagonalResidual.lean"),
            dependencies=("S9_CORRECTION_CYCLE",), forcing_exposure="flat local residual",
            if_removed="No smooth terminal forcing extension can be inferred at the singular point.",
        ),
        ResidualAtom(
            "S10_SPATIAL_LOCALIZATION", "whole-space", "compact-set", "velocity/pressure",
            "spatial_localization", "Multiplies potentials/fields by spatial cutoffs to obtain compact spatial support while preserving incompressibility.",
            _s("10.1", 118, "Proposition 10.1 localizes the local field to a compact set."),
            dependencies=("S9_FLAT_SUM",), forcing_exposure="direct through cutoff derivatives",
            if_removed="Compact support is lost, but an alternative global decay construction could replace it.",
        ),
        ResidualAtom(
            "S10_TEMPORAL_CUTOFF", "whole-space", "early-time", "velocity",
            "temporal_cutoff", "Uses a temporal cutoff to enforce zero initial data.",
            _s("10.1", 118, "Temporal cutoff gives zero initial datum."),
            dependencies=("S10_SPATIAL_LOCALIZATION",), forcing_exposure="direct through cutoff derivatives",
            if_removed="Initial data need not be zero; this is potentially acceptable for an unforced target.",
        ),
        ResidualAtom(
            "S10_FORCE_RESIDUAL", "whole-space", "compact-set", "momentum",
            "localized_force", "Defines the physical force as the exact residual of the localized fields, including all cutoff derivatives.",
            _s("10.1", 118, "Equation (10.5): f = R(u,p)."),
            dependencies=("S10_SPATIAL_LOCALIZATION", "S10_TEMPORAL_CUTOFF"), forcing_exposure="definition of final force",
            if_removed="For an unforced construction one must instead make the entire localized/global residual vanish identically.",
        ),
        ResidualAtom(
            "S10_FORCE_EXTENSION", "whole-space", "terminal-slice", "force jets",
            "terminal_extension", "Shows every force derivative has a compatible limit at t=1 and extends to a smooth compactly supported force.",
            _s("10.2", 118, "Lemma 10.2 gives uniform limits of every force derivative.",
               "NavierStokes/JointResidualLimits.lean"),
            dependencies=("S9_FLAT_SUM", "S10_FORCE_RESIDUAL"), forcing_exposure="regularizes final force",
            if_removed="The current forced theorem loses smooth extension through the singular time.",
        ),
        ResidualAtom(
            "S10_BREAKDOWN_TRANSFER", "whole-space", "global", "theorem",
            "uniqueness_transfer", "Transfers local velocity growth to any hypothetical global bounded-energy smooth solution with the same data/force.",
            _s("10", 116, "Comparison/uniqueness yields whole-space breakdown.",
               "NavierStokes/ComparatorR3Theorem.lean", "navier_stokes_breakdown_R3"),
            dependencies=("S10_FORCE_EXTENSION",), forcing_exposure="none",
            if_removed="Construction no longer proves the comparator breakdown statement.",
            evidence=EvidenceLevel.FORMALIZED,
        ),
    ]


def mechanisms() -> list[Mechanism]:
    atoms = {a.id: a for a in residual_atoms()}
    groups = {
        "similarity_profile": ("geometry", "Creates singular core", "indirect", False,
                               "Find another singular background satisfying the needed local balances."),
        "annular_stress": ("geometry", "Packages base mismatch", "high if uncancelled", True,
                           "Choose a profile with smaller/zero annular stress or another internal momentum-flux mechanism."),
        "heat_exterior": ("globalization", "Exact zero-residual exterior", "lowers exposure", True,
                          "Construct another global/decaying exact or sufficiently flat exterior."),
        "higher_order_base": ("correction", "Removes base residual orders", "prevents singular forcing", True,
                              "Solve base equations more exactly or replace the all-order correction scheme."),
        "support_separation": ("wave", "Suppresses cross-label interactions", "none", True,
                               "Control cross interactions analytically instead."),
        "pulse_seeding": ("forcing", "Creates pulse amplitudes", "direct", True,
                           "Encode pulses in initial data or derive them endogenously from a nonzero source generated by the flow."),
        "amplify_then_damp": ("wave", "Amplify stress carriers and erase tails", "none after seed", True,
                              "Provide another pulse dynamics with growth, stress delivery, and flat decay."),
        "stress_cone": ("wave", "Realizes annular stress internally", "removes singular-force need", True,
                        "Eliminate the target stress in the base or realize it by another nonlinear covariance/stress mechanism."),
        "curl_realization": ("constraint", "Exact incompressibility of waves", "none", True,
                             "Use another exactly divergence-free parameterization."),
        "mean_corrections": ("correction", "Zero-mode repair", "prevents leakage", True,
                             "Choose oscillations/profile so zero-mode residuals vanish intrinsically."),
        "moment_repair": ("correction", "Preserves support/exterior moments", "prevents leakage", True,
                          "Change exterior/globalization or design corrections in the constraint nullspace."),
        "correction_cycle": ("correction", "Improves residual order", "prevents singular force", True,
                             "Find a closed-form/exact solution or a faster convergent correction scheme."),
        "flat_summation": ("correction", "All-jet flat local residual", "permits smooth force", True,
                           "Make residual exactly zero or prove terminal smoothness another way."),
        "spatial_localization": ("forcing", "Compact spatial support", "direct cutoff derivatives", True,
                                 "Use a global decaying construction and avoid spatial cutoff derivatives."),
        "temporal_cutoff": ("forcing", "Zero initial data", "direct cutoff derivatives", True,
                            "Allow nonzero smooth initial data, which is compatible with the unforced regularity problem."),
        "localized_force": ("forcing", "Final exact residual", "is the final force", True,
                             "For an unforced target prove the exact residual vanishes identically."),
        "terminal_extension": ("forcing", "Smooth compact force through t=1", "regularity", True,
                               "Irrelevant if force is identically zero; otherwise replace extension argument."),
        "uniqueness_transfer": ("theorem", "Converts candidate into breakdown", "none", False,
                                "Need an equivalent contradiction/continuation theorem."),
    }
    out = []
    for mid, (cat, role, exposure, repl, obligation) in groups.items():
        req = tuple(a.id for a in atoms.values() if a.mechanism == mid)
        out.append(Mechanism(mid, cat, role, exposure, req, repl, obligation))
    return out
