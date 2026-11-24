import YM.QCD.Orbit.Foil

/-!
# uniform stationary birth call with many actual sources. Forest transitory, does not infect array. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Orbit.Birth
open Lat Lattice Wilson Kit Cost Function Finset Tree RG Metric Filter Pine Rudder
open Precision Stationary Eyrie Run Revolve Flume Sparks Quarry YM.Next.Free YM.Further.PhysicalPeriodLimitF933 Macrame
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff BigOperators Classical
variable {T : Type*} {j k N : ℕ}{P : T→Flight j k}{Δ O Q K : ℝ}{C : KernelChoices}{p : Clip}{H : T→PathData su}
    {S : T→SparkMesh} (Z : ∀ i, Place (P i) C (S i) (H i) p O Q)
def stand (S:T→SparkMesh)(P:T→Flight j k) (C:KernelChoices) : Works (T×ℕ):={ n:=fun i=>high (P i.1) (S i.1) i.2,s:=fun i=> (S i.1).n i.2,ratio:=fun i=> (act (P i.1) C (S i.1) i.2).ratio }
variable (B:Plan j)(L:Plan k)
variable (E:Patch) (hE:∀ i,(P i).patch=E) (M: Push.Uniform.Before su O Q E.J C N)
local notation "X"=>stand S P C
include Z hE
theorem quays : ∃ Y:Quay X C E p M, Y.step=(fun i:T×ℕ=> act (P i.1) C (S i.1) i.2) ∧ Y.path=(fun i:T×ℕ=> H i.1) := by
  let s (i:T×ℕ):StepData ((X).s i) ((X).n i):= act (P i.1) C (S i.1) i.2
  let H' (i:T×ℕ):= (Z i.1).forest i.2
  have hP i: (s i).patch=E:= hE _
  choose u hu using fun i:T×ℕ=>Push.Uniform.Before.graph (S:=s i) (H' i) M ((Z i.1).paid) ((Z i.1).admiss i.2) (by rw [hP i]) rfl
  exact ⟨⟨s,fun i=>rfl,hP,fun i=>rfl,H',u,fun i=> H i.1,fun i=> (Z i.1).admiss i.2,fun i=> (Z i.1).value,fun i=>(Z i.1).paid,hu⟩, rfl,rfl⟩ -- worry Y.path, need record in thm

variable {D: ∀ (_:T)(f:Side), Grid f→ Sheet f}
omit hE in
lemma forum {Y: Quay X C E p M}(hP: Y.step=(fun i:T×ℕ=>act (P i.1) C (S i.1) i.2))(hk: Y.path=(fun i:T×ℕ=> H i.1)) (hu : ∀ i,Vital (D i)) (i:T)(n:ℕ) :
    pulseShift (Z i) B (D i) n =ᶠ[𝓝 0] (fun x=> shiftL (P i) (divides0 (P i) (S i) n) B (D i _) (Y.forge (i,n) x)):=by
  let S':=(act (P i) C (S i) n)
  let F:=shiftL (P i) (divides0 (P i) (S i) n) B (D i _)
  have he : Y.step (i,n)=S':=congr_fun hP _
  have hR : Rooted S' F:=fun k v=> shiftK _ B _ (D i _) (fun U k => (hu i|>.1 _).1 k U) _ _
  let W:= Y.tree (i,n); have hj:= Y.issued (i,n)|>.critical
  have hp' := Y.bounds (i,n)
  obtain ⟨hp0,hz,-⟩:= M.full_pack (S:=Y.step (i,n)) W (Classical.arbitrary (Y.step (i,n)).Choices) hp' (Y.admiss _) (by rw [Y.sig]) (Y.used _)
  -- equality does dependent rec. mirror argument comparing actual critical branch with Y critical and a same S payload budget. local lemma generalize with s'.
  have hu {s : StepData ((X).s (i,n)) ((X).n (i,n))} (he:s=S') (w:Forest s.ratio) (ρ: Bid.Dir su _ → AxisChart su w) (h: Critical w p (H i) ρ) (hq:PriceGap w p (H i) (M.tables p (s.patch)).gap) (hz:0<(M.tables p (s.patch)).gap) :
      pulseShift (Z i) B (D i) n =ᶠ[𝓝 0] (fun x=> F (encamp w ρ x).1):=by
    subst s
    let t:=Classical.arbitrary S'.Choices; exact (panorama h t ((Z i).admiss n).1 ((Z i).paid) hq hz hR ((Z i).critical n)).symm
  rw [hk] at hj hp0; exact hu he _ _ hj hp0 hz
include Z
lemma on_bills (hV : ∀ y:T,Vital (D y))
    (hU : ∀ Y:Quay X C E p M,(X).League (A:=true) (B:=true) fun i x=> D i.1 _ (Y.forge i x)) :
    ∃ w d,0<w∧0 ≤ d∧∀ (i:T)(j:ℕ), glyph (traceG _) Push.Uniform.bolt (Prod.fst (β:=Fiber)) Prod.fst (launch (Z i) B L (D i) j) w d:=by
  obtain ⟨Y,hy,hR⟩:=quays Z E hE M
  let V (i:T×ℕ):= P i.1
  have hpY i : (V i).patch=E:=hE _
  let P₀ (i:T×ℕ) := shiftL (V i) (Y.ratio_info hpY i) B (D i.1 ((X).n i))
  let J:(X).Board false false:=fun i x=> P₀ i (Y.forge i x)
  have hh :(X).League J:=by
    have h:= Y.citizens hpY B (U:=fun i=> D i.1 ((X).n i)) (hU Y) (fun i=> (hV i.1|>.1 _).2.2.2.1)
    exact (Works.League.identity _ _).down (((Y.moors hpY).connects h).connects (Y.moors hpY|>.up))
  obtain ⟨w,d,h,hD,Hw⟩:= metropolis L (fun i=>(V i).land) hh
  refine ⟨w,d,h,hD,fun i j k l=>?_⟩
  apply (Hw (i,j) k l).aliasG; filter_upwards [forum Z B E M hy hR hV i j] with x hx; unfold launch; rw [Pi.sub_apply, Pi.sub_apply,hx]; rfl
end YM.QCD.Orbit.Birth
