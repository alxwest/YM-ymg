import Mathlib

noncomputable section
open MeasureTheory
namespace GaussianField
abbrev FinLatticeSites (d : ℕ) (N : ℕ) := Fin d → ZMod N
end GaussianField
open GaussianField
variable (d N : ℕ)

structure LatticeLink (d : ℕ) (N : ℕ) where
  site : FinLatticeSites d N
  dir : Fin d
  deriving DecidableEq

/-- Shift a site by +1 in direction μ. -/
def siteShift (x : FinLatticeSites d N) (μ : Fin d) :
    FinLatticeSites d N :=
  Function.update x μ (x μ + 1)

/-- Shifts in different directions commute. -/
theorem siteShift_comm (x : FinLatticeSites d N) (μ ν : Fin d) (h : μ ≠ ν) :
    siteShift d N (siteShift d N x μ) ν = siteShift d N (siteShift d N x ν) μ := by
  ext i
  simp only [siteShift, Function.update]
  split_ifs with h1 h2 h3 h4 <;> subst_eqs <;> simp_all

/-- Target of a link. -/
def LatticeLink.target {d N : ℕ} (l : LatticeLink d N) :
    FinLatticeSites d N :=
  siteShift d N l.site l.dir

/-- A plaquette (oriented 2-cell): site + two ordered directions. -/
structure LatticePlaquette (d : ℕ) (N : ℕ) where
  site : FinLatticeSites d N
  dir1 : Fin d
  dir2 : Fin d
  h_lt : dir1 < dir2
  deriving DecidableEq

/-- The four boundary links of a plaquette (counterclockwise). -/
def LatticePlaquette.boundaryLinks {d N : ℕ}
    (p : LatticePlaquette d N) : Fin 4 → LatticeLink d N
  | 0 => ⟨p.site, p.dir1⟩
  | 1 => ⟨siteShift d N p.site p.dir1, p.dir2⟩
  | 2 => ⟨siteShift d N p.site p.dir2, p.dir1⟩  -- reversed
  | 3 => ⟨p.site, p.dir2⟩                        -- reversed

variable {G : Type*} [Group G] {d N : ℕ}

def GaugeConnection (G : Type*) (d : ℕ) (N : ℕ) := LatticeLink d N → G

def plaquetteHolonomy (U : GaugeConnection G d N) (p : LatticePlaquette d N) : G :=
  let l := p.boundaryLinks
  U (l 0) * U (l 1) * (U (l 2))⁻¹ * (U (l 3))⁻¹

def GaugeTransform (G : Type*) (d : ℕ) (N : ℕ) := GaussianField.FinLatticeSites d N → G

def gaugeTransformConnection (g : GaugeTransform G d N)
    (U : GaugeConnection G d N) : GaugeConnection G d N :=
  fun l => g l.site * U l * (g l.target)⁻¹

class HasGaugeTrace (G : Type*) (n : ℕ) [Group G] where
  rep : G →* Matrix (Fin n) (Fin n) ℂ

/-- Complex trace of a group element in the gauge representation. -/
def gaugeTrace (G : Type*) (n : ℕ) [Group G] [HasGaugeTrace G n] (g : G) : ℂ :=
  Matrix.trace (HasGaugeTrace.rep (G := G) (n := n) g)

/-- Real part of the trace. -/
def gaugeReTr (G : Type*) (n : ℕ) [Group G] [HasGaugeTrace G n] (g : G) : ℝ :=
  (gaugeTrace G n g).re

/-- Wilson action integrand: Re Tr(I - U_p) = n - Re Tr(U_p). -/
def wilsonPlaquetteCost (G : Type*) (n : ℕ) [Group G] [HasGaugeTrace G n] (Up : G) : ℝ :=
  ↑n - gaugeReTr G n Up


variable (G : Type*) [Group G] [MeasurableSpace G]

instance instMeasurableSpaceGaugeConnection (d N : ℕ) :
    MeasurableSpace (GaugeConnection G d N) := MeasurableSpace.pi

class HasHaarProbability (G : Type*) [MeasurableSpace G] where
  haar : Measure G
  isProb : IsProbabilityMeasure haar

attribute [instance] HasHaarProbability.isProb

variable [HasHaarProbability G]

/-- The Haar probability measure on G. -/
def haarG : Measure G := HasHaarProbability.haar (G := G)

instance : IsProbabilityMeasure (haarG G) := HasHaarProbability.isProb

variable (n : ℕ) [HasGaugeTrace G n]
variable (d N : ℕ) [Fintype (LatticeLink d N)]

def productHaar : Measure (GaugeConnection G d N) :=
  Measure.pi (fun _ : LatticeLink d N => haarG G)

def wilsonAction (β : ℝ) (U : GaugeConnection G d N)
    (plaq : Finset (LatticePlaquette d N)) : ℝ :=
  ∑ p ∈ plaq, β * wilsonPlaquetteCost G n (plaquetteHolonomy U p)

def boltzmannWeight (β : ℝ) (U : GaugeConnection G d N)
    (plaq : Finset (LatticePlaquette d N)) : ℝ :=
  Real.exp (-(wilsonAction G n d N β U plaq))

def partitionFn (β : ℝ) (plaq : Finset (LatticePlaquette d N)) : ℝ :=
  ∫ U, boltzmannWeight G n d N β U plaq ∂(productHaar G d N)

def ymDensity (β : ℝ) (plaq : Finset (LatticePlaquette d N))
    (U : GaugeConnection G d N) : ℝ :=
  boltzmannWeight G n d N β U plaq / partitionFn G n d N β plaq

def ymMeasure (β : ℝ) (plaq : Finset (LatticePlaquette d N)) :
    Measure (GaugeConnection G d N) :=
  (productHaar G d N).withDensity
    (fun U => ENNReal.ofReal (ymDensity G n d N β plaq U))
