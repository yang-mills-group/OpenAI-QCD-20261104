import YM.MassiveQCD.Evolution.ViewPort
import YM.MassiveQCD.Evolution.Payment
import YM.MassiveQCD.Cabaret.PureGas
import YM.QCD.Kites.Bake
/-! # Coefficient stalls for forced receipts *after* e.g. Ruby merger.
 Includes all spin-post invoices under published exponent and `Metric.ball 0 (1/2)`,
 cost contraction to z in unit disk, and permits thereafter. No varying hits with poses
 when assembling coefficient budget in `Prize`.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Ruby
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open MassiveQCD.Analysis.Shelf Metric
variable {c:Side}{N n B:ℕ}{t s r δ T τ u :ℝ}{i:Site c} {ι : Type}
local notation "Ω"=> EvenA c N
-- structured permanent turns (power upgrade no K K ambiguity). K to include full W.R.
structure LanternK (c:Side)(N:ℕ)(ι:Type) where
 bud:ι→ Cove.Hat c
 actsK: ℂ→ ι→Grid c→ EvenA c N
namespace LanternK
variable (Y: LanternK c N ι) (i:ι)
abbrev T' : Set ℂ :=Metric.ball 0 1
def get (z:ℂ) : Patron.Rail c N ι:=⟨Y.bud,Y.actsK z⟩
-- assemblies evaluate within Y.Goods
structure ChargedK (u r t T:ℝ)(B:ℕ)(δ τ:ℝ) :Prop where -- T reserved
  system:0< τ
  temp : ∀ z:ℂ,z∈ T' → Rail.Reg (Y.get z) r
  power : ∀ z:ℂ,z∈ T' → Quits (Y.get z) B u τ δ t
  aura : ∀ j x, Roof (fun z=>Y.actsK z j x)
variable (Hq : Y.ChargedK u r t T B δ τ)
-- φ^j absorption. Exposed coeffs real-axis and Borel per holds.
noncomputable def phased (s:ℝ) : Patron.Rail c N (ι×ℕ):= ⟨Y.bud ∘ Prod.fst,fun i V=> (s:ℂ)^i.2 • ampK (fun y=>Y.actsK y i.1 V) i.2⟩
variable (u':ℝ) (z:ℂ)
local notation "Y!"=> Y.phased u'
lemma aT {K:Ω→+*Ω} (hp:Continuous K)(i j) (U V:Grid c)(H:∀ x:ℝ, |x|<1→ K (Y.actsK x i U)=Y.actsK x j V) (hf : Roof fun z=>Y.actsK z i U)(hg:Roof fun z=>Y.actsK z j V)(n:ℕ): K ((Y!).warp (i,n) U)= (Y!).warp (j,n) V:=by
    let f x:=Y.actsK x i U; let g x:=Y.actsK x j V
    have ht: K (ampK f n)=ampK g n:= confirms n hf hg (K.toAddMonoidHom.toRealLinearMap hp) H
    change K ((u':ℂ)^n • _)=(u':ℂ)^n • _; rw [← Complex.ofReal_pow]; rw [Complex.coe_smul,Complex.coe_smul,eSM _ hp, ht]
include Hq
lemma regS : (Y!).Reg r:=by
    constructor
    · rintro ⟨i,j⟩ U V hV hx; apply congr_arg ((u':ℂ)^j • ·); exact confirms _ (Hq.aura i _) (Hq.aura i _) (ContinuousLinearMap.id ..) (fun x hx0=>Rail.Reg.uses (Hq.temp _ ((swim x).2 hx0)) i U V hV hx)
    · rintro ⟨i,j⟩; exact (measurable_const (a:=(u':ℂ)^j)).smul (stockB (fun V z=>Y.actsK z i V) j (Hq.aura i) (fun x hx=> (Hq.temp x ((swim x).2 hx)).reads i))
    · rintro ⟨i,j⟩ U; let A:= (Y.bud i).place; let P x:=Y.actsK x i U
      obtain ⟨V,hV⟩:=Territory.solvent (N:=N) A
      apply (hV _).2; change (u':ℂ)^_ • _∈ V; rw [← Complex.ofReal_pow,Complex.coe_smul]; exact V.smul_mem _ (closed_tier j V (Submodule.closed_of_finiteDimensional V) (Hq.aura i U) (fun x hx=>(hV _).1 ((Hq.temp x ((swim x).2 hx)).role i U)))
    rintro ⟨i,j⟩ U h; by_contra hv; apply h
    let N':=EvenA c N; have hh : ampK (fun y=>Y.actsK y i U) j=0:=by
       let V:= (⊥: Submodule ℝ (EvenA c N)); apply (Submodule.mem_bot ℝ ..|>.mp)
       refine closed_tier j V (Submodule.closed_of_finiteDimensional V) (Hq.aura i U) ?_
       intro x hx; apply Submodule.mem_bot ℝ |>.mpr
       by_contra hk; exact hv ((Hq.temp x ((swim x).2 hx)).buys i U hk)
    change (u':ℂ)^j • ampK _ _=0; rw [hh,smul_zero]
-- Strong type for preserving a particular tag. Spinning K.
structure Tracks (Y:Patron.Rail c N ι)(p:ι→ℕ) : Prop where
  movesK s z k: Warrant s z k→∃ e:Equiv.Perm ι,∀ i,p (e i)=p i ∧
    (((Y.addr (e i)).place=(Y.addr i).place.image (act s)) ∧ (Y.addr (e i)).inv=(Y.addr i).inv.image (act s) ∧∀ U:Grid c, Diode N s k z (Y.warp i (sky s U))= Y.warp (e i) U)
lemma tracks [Countable ι](hv:∀ x:ℝ, |x|<1 → MixedInk (Y.get x)): Tracks (Y!) Prod.snd:=by
    constructor; intro s z k h
    let f (p:ι×ι)(V:Grid c)(y:ℂ):=Diode N s k z (Y.actsK y p.1 (sky s V)); let g (p:ι×ι)(V:Grid c)(y:ℂ):=Y.actsK y p.2 V
    let K:=(Diode N s k z); let T: EvenA c N →L[ℂ]EvenA c N:= LinearMap.toContinuousLinearMap { toFun:=K, map_add':=map_add _, map_smul':=fun c i=>swayC .. }
    obtain ⟨x,hX,hψ⟩:= MassiveQCD.Analysis.Shelf.generic f g (fun i j k hk=>(T.analyticAt _).comp (Hq.aura i.1 (sky s j) k hk)) (fun i j=> Hq.aura i.2 j)
    obtain ⟨p,hp⟩:= (hv x hX).moves s z k h; have hh (i:ι)(V:Grid c)(y:ℝ)(hy:|y|<1): K (Y.actsK y i (sky s V))=Y.actsK y (p i) V:= hψ (i,p i) (fun V=>(hp i).2.2 V) V ((swim y).2 hy)
    refine ⟨Equiv.prodCongr p (Equiv.refl ℕ),?_⟩; rintro ⟨i,n⟩; exact ⟨rfl, (hp i).1,(hp i).2.1,fun U=> aT Y u' (phare _) _ _ _ _ (hh i U) (Hq.aura _ _) (Hq.aura _ _) n⟩ -- picks preserve power? future K needs `D.Tag` maybe at assembling pure.Enn λ. Include before collapsing. edit
lemma colors [Countable ι](hv:∀ x:ℝ,|x|<1 → MixedInk (Y.get x)): MixedInk (Y!):=by
    have ht (K: Ω→+*Ω)(hz:Continuous K)(i:ι)(V U: Grid c)(he:∀ x:ℝ, |x|<1→ K (Y.actsK x i U)=Y.actsK x i V)(p:ℕ): K ((Y!).warp (i,p) U)=(Y!).warp (i,p) V:=by apply aT Y u' hz i i U V he (Hq.aura i U) (Hq.aura i V) p
    constructor
    · rintro ⟨i,p⟩ U k; exact congr_arg Subtype.val (ht (sways (Lat.rotates N k)) (phare _) i U _ (fun x h=>Subtype.ext ((hv x h).gauge i U k)) p)
    · rintro ⟨i,p⟩ V k h; exact ht _ (phare _) i V V (fun x hx=> (hv x hx).num i V k h) p
    · rintro ⟨i,p⟩ V; exact ht _ (phare _) i V V (fun x h=>(hv x h).real i V) p
    intro s z k h; obtain ⟨e,he⟩:=(tracks Y Hq u' hv).movesK _ _ _ h; exact ⟨e,fun i=> (he i).2⟩
end LanternK
end YM.QCD.Ruby
