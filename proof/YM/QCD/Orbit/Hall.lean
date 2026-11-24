import YM.QCD.Orbit.Pave

/-!
# single mesh purchases station jets with budget order. Families can choose different critical graphs. Reaches independent germs. For interaction use particular visually meaningfully supported representatives later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Orbit
open Lat Lattice Wilson Kit Cost Function Finset Tree RG Metric Filter Pine
open Precision Stationary Eyrie Run Revolve Flume Sparks Quarry YM.Next.Free YM.Further.PhysicalPeriodLimitF933 Macrame
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff BigOperators Classical
variable {f c : Side} {j k x: ℕ}{B:Plan j}(P: Flight j k)(K:KernelChoices)(T:SparkMesh)(W:PathData su) (p:Clip) {a b t C:ℝ}
abbrev soffit (P:Flight j k) (c:Side) : Side:= c * P.L
abbrev high (i:ℕ):=soffit P (T.n i)
lemma divides0 (i): (high P T i).val=(T.n i).val*P.L.val:=rfl
abbrev act (i:ℕ):= Venue P K (divides0 P T i)

namespace Birth
variable {P K T p W}
structure Place (P:Flight j k) (K:KernelChoices) (T:SparkMesh) (W:PathData su) (p : Clip) (a C:ℝ) where
 forest (i:ℕ): Forest (act P K T i).ratio
 u (i:ℕ) : Bid.Dir su (T.n i)→ AxisChart su (forest i)
 critical i : Critical (forest i) p W (u i)
 admiss i : Bid.Larger (G:=su) (act P K T i)
 value : ℝ
 paid : W.Bounds p a C value
-- no LP.P Beam commitments yet, pure viable permit
variable (Z: Place P K T W p a C)
variable {U: (f:Side)→ Grid f→Sheet f}
def Vital (D:(f:Side)→Grid f→Sheet f):Prop:= (∀ f,Blank (D f)) ∧∀ {f F:Side}{N:ℕ}(L:Window f F N)(p:Site F→ℂ)(_ : Quaint L p)(U:Grid f), D F (L.links U)*stream L p=stream L p*D f U

def pulseShift (B:Plan j) (D:(f:Side)→Grid f→Sheet f):T.Field:=fun i=> mirage (Z.forest i) (shiftL P (divides0 P T i) B (D _)) (Z.u i)
def launch (B:Plan j)(L:Plan k)(D:(f:Side)→Grid f→Sheet f):T.Field:=pulseShift Z B D- fun i=> castF (n:=T.n i) (fun U=>wood L 0 P.land U)
lemma bears {i l}(h: i≤l): (high P T l).val=(high P T i).val*T.ratio i l:= by change (T.n l).val*P.L.val= _; rw [T.factor _ _ h]; rw [divides0]; ring

lemma phase (L:Plan k) (hV:Vital U)(he:∀ i,ContDiffAt ℝ ω (launch Z B L U i) 0): Clan T (launch Z B L U) ∧∀ i,Noble (launch Z B L U i):=by
  have hc:= wood_prism L P.land T
  let f (i:ℕ):= pulseShift Z B U i
  let I i:=castF (n:=T.n i) (fun U=>wood L 0 P.land U)
  let A:= Classical.choice (Push.Uniform.pre_order su a C P.patch.J K (show 3 ≤ 3 from le_refl _))
  have ht (i) : Priest (f i) ∧ Noble (f i):=by
    have hs : ContDiffAt ℝ ω (f i-I i) 0:= he i
    obtain ⟨hQ,hp,-⟩:= A.full_pack (S:=act P K T i) (Z.forest i) (Lace.plain K) Z.paid (Z.admiss i) rfl rfl
    refine conduct (P:=P) (Z.critical i) (Z.admiss i) Z.paid hQ hp B (hV.1 _) (by
      change ContDiffAt _ _ (f i) _; have HH:ContDiffAt ℝ ω ((f i-I i)+I i) 0:= ContDiffAt.add hs (hc.way i|>.ready); simpa using HH)
  refine ⟨Clan.less (show Clan T _ from ⟨fun i=>(ht i).1,fun i j he=>?_⟩) hc,fun i=> (ht i).2.less (driver L _ _|>.told)⟩
  let L:= Macrame.Lace.project (h:=divides0 P T i) (P:=P.patch) (H:=divides0 P T j) (T.factor _ _ he) (Z.admiss i|>.2.2)
  have hF : L.low=T.vista i j he:=rfl
  obtain ⟨d,hq⟩:= twinkle L.high (bears he) (T.parity i j he)
  let V := d∘ L.R.embed
  have hp : Quaint (T.vista i j he) V := hF ▸ descend P L hq
  refine ⟨V,hp,?_⟩
  let D:=U (high P T j); let d':= U (high P T i)
  have H : Rooted (act P K T j) (shiftL P (divides0 P T j) B D):=fun k p=> shiftK _ _ _ _ (fun x k=> (hV.1 _).1 k x) p k
  have hh(Y:Cnr (T.n i)→Grid (high P T i))(hy:Army Y 0)(hv:Y 0=1):
      ∀ᶠ x in 𝓝 0, shiftL P (divides0 P T j) B D (L.high.links (Y x))*stream L.low V=stream L.low V*shiftL P (divides0 P T i) B d' (Y x):=by
    let G q:=L.high.links (Y q); have hg : Army G 0:= fun _=> hy _
    filter_upwards [neighbo P B _ (hV.1 _) hy hv,neighbo P B _ (hV.1 _) hg (show G 0=1 by unfold G; rw [hv]; rfl)] with x ha he'; exact panels P B L d' D d hq (Y x) ha he' (hV.2 L.high d hq (Y x)) -- inspect
  have hv:= faceted P.patch K (T.factor _ _ he) (Z.admiss i|>.2.2) (Z.critical i) (Z.critical j) Z.paid (Z.admiss _) H V hh
  exact hv

lemma shoots (L:Plan k) (h : Vital U)(i:ℕ): launch Z B L U i (0:Cnr (T.n i))=0:=by
  let R:= Z.critical i; unfold launch; rw [Pi.sub_apply, Pi.sub_apply,pulseShift,Quarry.mirage, encamp_zero R]
  simp only [Prod.fst_one,castF,Function.comp_apply,input_zero,sub_eq_zero]; unfold shiftL shiftH; rw [show U _ 1=0 from (h.1 _).2.2.2.1, add_zero, tree_zero, bare_this]; exact heir ..
end Birth
end YM.QCD.Orbit
