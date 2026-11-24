import YM.Massive.Filament.Shutters
import YM.Massive.Filament.Foil
import YM.Massive.Pith.Monitor
/-! # Supports & gauges through harmonic expansion
K budget paid in `Filament.Loop`. K basis choices don't vary across z,s. All four-strut coverage maps must also work on real radius. No estimates here for Borel kernels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fibre
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Kites
open Massive.Filament Ruby Fused
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N B:ℕ}{h A R C D W r:ℝ}{s z:ℂ} {ι α: Type}
variable (X: ℂ → ℂ → Rail c N ι)
-- Geometry wall flag.Stear.Poles
local notation "Q"=> EvenA c N
local notation "D"=> Grid c
variable (Z:Ruby.Hue c N α)(Y:Rail c N ι)
-- symmetry.Accounts separate translations + unmarked only.Fit.
structure Grit (U:Grid c→EvenA c N) :Prop where
 gauge : shadeG U
 flex x: Pith.Phases (U x)
 real x: Regal c N (U x)=U x

def Swing (p: Strut c) (k: Spike) (g: Site c→ℂ) (w: Equiv.Perm ι) (X:Rail c N ι) :Prop:= ∀ i,
               ((X.addr (w i)).place=(X.addr i).place.image (act p)) ∧ (X.addr (w i)).inv=(X.addr i).inv.image (act p) ∧∀ U:Grid c, Diode N p k g (X.warp i (sky p U))= X.warp (w i) U
structure Charm (X:Rail c N ι) :Prop where
 tone i: Grit (X.warp i)
 turn p k g: Warrant p g k → ∃ w,Swing p k g w X
-- easier to carry actual ↑(s:ℝ) on whole $z∈$ disk.Strict.Simpler. Need probably preserve for distances upto 1.
structure MatchX (X:ℂ→Rail c N ι) : Prop where
 life (z:ℝ) (i:ι): ‖z‖< (1:ℝ) → Grit ((X z).warp i)
 trueShift (p:Strut c)(k:Spike)(g: Site c→ℂ): Warrant p g k→∃ w:Equiv.Perm ι,∀ z:ℝ, ‖z‖<1→Swing p k g w (X z)
lemma gear (h: MixedP Y): Charm Y:=⟨fun i=> ⟨h.gauge i,fun U=>Pith.fitP _ (h.num i U),h.real i⟩,fun p k g h' => h.moves p g k h'⟩
lemma grip (X: D→Q) (h:Grit X)(u:ℝ): Grit (fun V=>u • X V):=
 ⟨(fun U k=>congr_arg Subtype.val ((eSM (sways (Lat.rotates N k)) (phare _) u (X (gauge k U))).trans (congr_arg (u • ·) (show sways _ _=X U from Subtype.ext (h.gauge U k))))),fun U=>Pith.phase_r _ _ (h.flex U),fun U=>(eSM _ (phare _) u (X U)).trans (congr_arg (u • ·) (h.real U))⟩
lemma portCL (K:Q →+*Q)(ht:Continuous K) (i j: ι): Shutter (fun f=> K (f i)=f j):=by
    let L:Q→L[ℝ]Q:=LinearMap.toContinuousLinearMap {toFun:=K,map_add':=map_add _,map_smul':=fun r x=>eSM _ ht _ _}; exact Shutter.fx L (ContinuousLinearMap.id ..) i j
lemma shut_g (U:Support c)(x:Grid c) : Shutter (fun f:Grid c→EvenA c N=> Gated U (f x)) :=by
    obtain ⟨Z,hZ⟩:= Territory.solvent U (N:=N)
    exact (Shutter.land Z Z.closed_of_finiteDimensional x).transfer fun f=> (hZ _).symm
lemma pressure (n:ℕ)(hp:Arc X)(t:ℝ)(hq:‖s‖<1)(hr:∀ z:ℝ, ‖z‖<1→ (X z s).Reg t): (beadK X n s).Reg t := by
     let P(i:ι)(U:Grid c)(z):= (X z s).warp i U
     let B(i):= (X 0 0).addr i; have ht i U:Holo (P i U):= (hp.reading i U).wire _ hq
     refine ⟨fun i U V he hg=>?_,fun i=>?_,fun i U=> ?_,?_⟩
     · have hT (x:ι): Shutter (fun f:Grid c→EvenA c N=>f U=f V):= Shutter.eq _ _
       refine Shutter.circlet n (hT i) (ht i) (fun z hz=> (hr z hz).uses _ _ _ ?_ ?_); all_goals rw [hp.brace _ _]; assumption -- he hg defeq
     · exact Shutter.circlet n Shutter.meas (ht i) (fun z hz=>(hr z hz).reads i)
     · refine Shutter.circlet n (shut_g (B i).place U) (ht i) (fun z hz=>?_); unfold B; rw [← hp.brace (z:ℂ) s]; exact (hr z hz).role i U
     intro i U he; contrapose! he; refine Shutter.circlet n (Shutter.flat U) (ht i) (fun z hz=>by_contra fun h=>he ?_); have hh:=(hr z hz).buys i U h; rw [hp.brace (z:ℂ) s] at hh; exact hh
lemma portClean (n:ℕ)(K:EvenA c N →+* EvenA c N)(ht: Continuous K) (p:ι→ℂ→EvenA c N)(i j:ι) (h:∀ i,Holo (p i)) (hx:∀ z:ℝ,‖z‖<1→ K (p i z)=p j z): K (bead n (p i))=bead n (p j) := Shutter.circlet n (portCL K ht i j) h hx
set_option maxHeartbeats 500000 in
lemma peaceG (n:ℕ)(hp:Arc X)(hq:‖s‖<1)(hr: MatchX (fun z=> X z s)): Charm (beadK X n s):=by
    let P i (U:Grid c)(z):=(X z s).warp i U; have ht i U : Holo (P i U):=(hp.reading i U).wire _ hq
    constructor
    · intro i; refine ⟨fun U k=> congr_arg Subtype.val (portClean n (sways (Lat.rotates N k)) (phare _) (P i) (gauge k U) U (ht i) fun z hz=> Subtype.ext ((hr.life z i hz).gauge U k)),fun U w hw=>?_,fun U=>?_⟩
      · exact portClean n (sways (flute (Lat.Row c) (Matrix.diagonal w))) (phare _) (P i) U U (ht i) fun z hz=> (hr.life z i hz).flex U w hw
      exact portClean n (Regal c N) (phare _) (P i) U U (ht i) fun z hz=> (hr.life z i hz).real U
    intro p k g hc; obtain ⟨w,hW⟩:= hr.trueShift p k g hc; refine ⟨w,fun i=>?_⟩
    have hW₀ (z:ℝ)(hz:‖z‖<1) : ((X 0 0).addr (w i)).place=((X 0 0).addr i).place.image (act p) ∧ ((X 0 0).addr (w i)).inv=((X 0 0).addr i).inv.image (act p) :=by
        have hg:= (hp.brace z s).symm; rw [hg]; exact ⟨(hW z hz i).1,(hW z hz i).2.1⟩
    refine ⟨(hW₀ 0 (by simp)).1,(hW₀ 0 (by simp)).2,fun U=>?_⟩
    exact portClean n (Diode N p k g) (phare _) (fun j:ι×Grid c=> P j.1 j.2) (i,sky p U) (w i,U) (fun j=> ht j.1 j.2) (fun z hz=> (hW z hz i).2.2 U) -- implicit p extraction?
lemma watt_reg (hr:Y.Reg h)(q:ℂ): (watt Y q).Reg h:=by
    refine ⟨fun i U V he hg=>congr_arg (q • ·) (hr.uses _ _ _ he hg),fun i=>(show Measurable (fun _:Grid c=>q) from measurable_const).smul (hr.reads i), fun i U=>?_, fun i U hi=> hr.buys i U fun he=> hi ((congr_arg (q • ·) he).trans (smul_zero q))⟩
    unfold Gated; rw [show (watt Y q).warp i U=q • Y.warp i U from rfl,map_smul]; exact Subalgebra.smul_mem _ (hr.role ..) q
lemma wattCharm (hr:Charm Y)(q:ℝ): Charm (watt Y q):=by
    have hZ (v:EvenA c N): (q:ℂ) • v=q • v:= IsScalarTower.algebraMap_smul ℂ q v
    refine ⟨fun i=> grip (Y.warp i) (hr.tone i) q, fun z k g hz=>?_⟩ -- defeq ℝ smul
    obtain ⟨w,hW⟩:=hr.turn z k g hz; exact ⟨w,fun i=>⟨(hW i).1,(hW i).2.1,fun U=> (eSM _ (phare _) q _).trans (congr_arg (q • ·) ((hW i).2.2 U))⟩⟩
lemma bunchCharm (P:α→Rail c N ι)(hp:∀ i, Charm (P i)): Charm (kaX P):=by
    refine ⟨fun i=> (hp i.1).tone i.2, fun z k g hz=>?_⟩
    choose w hw using fun i=> (hp i).turn z k g hz
    let W:Equiv.Perm (α×ι):= { toFun:=fun i=>(i.1,w i.1 i.2),invFun:=fun i=>(i.1,(w i.1).symm i.2),left_inv:=by intro i; exact Prod.ext rfl ((w i.1).left_inv i.2), right_inv:=by intro i; exact Prod.ext rfl ((w i.1).right_inv i.2)}
    exact ⟨W,fun i=>hw i.1 i.2⟩
lemma bunchReg (P:α→Rail c N ι)(hp:∀ i,(P i).Reg h): (kaX P).Reg h:=⟨fun i=> (hp i.1).uses i.2, fun i=>(hp i.1).reads i.2,fun i U=> (hp i.1).role i.2 U, fun i U=> (hp i.1).buys i.2 U⟩
lemma faintCharm (k r:ℝ)(hp:Arc X)(hq:‖s‖<1)(he:MatchX (fun z=>X z s))(hr:∀ z:ℝ, ‖z‖<1→ (X z s).Reg r): (∀ n,Charm (faint X n k s) ∧ (faint X n k s).Reg r)∧Charm (tail X k s) ∧ (tail X k s).Reg r:=by
    have hh (n:ℕ):Charm (faint X n k s):= by unfold faint; rw [←Complex.ofReal_pow]; exact wattCharm _ (peaceG X n hp hq he) _
    have h n: (faint X n k s).Reg r:=watt_reg _ (pressure X n hp r hq hr) _
    exact ⟨fun i=> ⟨hh i,h i⟩,bunchCharm _ fun i=> hh (i+2),bunchReg _ fun i=>h (i+2)⟩
end YM.QCD.Fibre
#print axioms YM.QCD.Fibre.peaceG
#print axioms YM.QCD.Fibre.faintCharm
