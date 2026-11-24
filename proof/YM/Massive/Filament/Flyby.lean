import YM.Massive.Filament.Orbit
import YM.Massive.Filament.Frost
/-! 
# Get actual K for the marker perturb continuation. No yet assuming reality or field rescaling or a width ⇒ launch. Formal harmonic θ family in same gas currency & equality representation using its Arc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fibre
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Kites
open Massive.Filament Ruby Fused
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N B:ℕ}{h t a A R C D W r:ℝ}{s z:ℂ} {ι α ν : Type}
local notation "Q"=> EvenA c N
variable (X:Rail c N ι) (Y:Rail c N α)(Z:Rail c N ν)
section fusion
-- symbolic address Prog Concept only needed for relocation.Elite packing choices; this supplies prices & area metadata.
def tie : Rail c N (ι⊕α):=⟨Sum.elim X.addr Y.addr, Sum.elim X.warp Y.warp⟩
def hueW (Z: Rail c N ι)(f:ι→ℂ): Rail c N ι:=⟨Z.addr,fun i v=> f i • Z.warp i v⟩
lemma budgetFuse (f:ι⊕α→ℝ)(hp:SumBudget (f ∘ Sum.inl) A)(h:SumBudget (f∘Sum.inr) R): SumBudget f (A+R):=by
    have he : HasSum f ((∑' i:ι,f (Sum.inl i)) + ∑' i:α,f (Sum.inr i)):= hp.2.1.hasSum.sum h.2.1.hasSum
    refine ⟨(fun i=>by rcases i with i|i; exact hp.1 _; exact h.1 _), he.summable, he.tsum_eq ▸ (add_le_add hp.2.2 h.2.2)⟩
lemma quitsTie (hp: Quits X B A R t h) (hE: Quits Y B C R t h) : Quits (tie X Y) B (A+C) R t h:=by
    obtain ⟨f,hf,hX⟩:=hp.cost; obtain ⟨g,hg,hY⟩:=hE.cost; let F:=tie X Y; let H:=Sum.elim f g; refine ⟨H,(fuelHit F _).mpr fun x=> budgetFuse (fun i=>fuelCharge F B R t x i*H i) ((fuelHit X _).mp hf x) ((fuelHit Y _).mp hg x),?_⟩
    rintro (i|i) U; exact hX i U; exact hY i U
lemma quitsH (f:ι→ℂ)(hf:∀ i, ‖f i‖ ≤W)(hp:Quits X B A R t h)(hv:0 ≤W): Quits (hueW X f) B (W*A) R t h:=by
   obtain ⟨q,hq,hT⟩:=hp.cost; let r i:=W*q i; let Z:= hueW X f; refine ⟨r,(fuelHit Z r).mpr fun x=> ?_, fun i v=>?_⟩
   · rw [show (fun i=> fuelCharge Z B R t x i*r i)=_ from funext (fun i=> (show _=W*(fuelCharge X B R t x i*q i) from mul_left_comm ..))]; exact budget_scale hv ((fuelHit X q).mp hq x)
   let L:= joule (c:=c) (N:=N) h; change ‖L (f i • _)‖≤ r i; rw [map_smul,norm_smul]; exact mul_le_mul (hf i) (hT i v) (norm_nonneg _) hv
lemma ensures (X:Rail c N ι)(ht:Quits X B A R t h)(he:1 ≤ R)(hf:0≤t)(hJ:1 ≤h) (U:Grid c): Summable (fun i=> ‖X.warp i U‖):=by
    obtain ⟨f,hf',hF⟩:=ht.cost; have hn : 0≤ f:=fun i=> (norm_nonneg _).trans (hF i 1)
    have hp (i:ι): f i≤ taxed (oriD X) f R i:= le_mul_of_one_le_left (hn i) (one_le_pow₀ he)
    exact (Loom.fishes _ _ hf' (fun i=> (hn i).trans (hp i)) hf (fun i _=> (X.addr i).alive.mono (X.addr i).part)).of_nonneg_of_le (fun _=> norm_nonneg _) (fun i=> (Loom.tore _ hJ).trans ((hF i _).trans (hp i)))
lemma lastK (Z:Rail c N ι)(t:ℝ)(V:Grid c)(hp:Summable (fun i=> ‖Z.warp i V‖)): Summable (Ruby.tK Z t V):=by
   refine Summable.of_norm_bounded (summable_finsetProd_of_summable_nonneg (fun i=>norm_nonneg (Z.warp i V)) hp) fun i=>?_; unfold Ruby.tK; split
   · exact Finset.norm_prod_le ..
   exact norm_zero.trans_le (prod_nonneg fun i _=> norm_nonneg _)
end fusion
namespace Harm
variable (H:ℂ→ℂ→Rail c N ι) (a:ℝ)
def vari (Z:Rail c N ν)(n:ν→ℕ)(z:ℂ): Rail c N ν:= hueW Z (fun i=> z^(n i))
def rosterH (d:ν→ℕ)(z:ℂ): Rail c N (ι⊕α⊕ν):= tie X (tie (watt Y z) (vari Z d z))
-- split assembly degrees.
abbrev Key (ι:Type):= ι ⊕ ι ⊕ ℕ×ι
def widthE (x:ℕ×ι) := x.1+2
def flux (s z:ℂ) : Rail c N (Key ι):= rosterH (H 0 0) (faint H 1 a s) (tail H a s) widthE z
def peak : Key ι→ι:= Sum.elim id (Sum.elim id Prod.snd)
lemma factorTie (d:ν→ℕ)(hX: Quits X B A R t h)(hY:Quits Y B C R t h)(hZ:Quits Z B D R t h)(hz:‖z‖≤1):Quits (rosterH X Y Z d z) B (A+(C+D)) R t h:=by
    have he:0≤C:=by obtain ⟨f,hf,_⟩:=hY.cost; exact budget_nonneg (hf 0)
    exact quitsTie _ _ hX (quitsTie _ _ (wattsLoosen _ (watt_price Y z hY) (mul_le_of_le_one_left he hz)) (wattsLoosen _ (quitsH _ _ (fun i=> (norm_pow z (d i)).trans_le (pow_le_one₀ (norm_nonneg _) hz)) hZ zero_le_one) ((one_mul D).le))) -- q exponent missing argument
omit a in
private lemma selectorOne (i:ι)(x:ι→EvenA c N): HasSum (fun j=> if j=i then x j else 0) (x i):=by simpa only [if_true] using hasSum_single i (f:=fun j=> if j=i then x j else 0) (fun j h=>if_neg h)
variable (U:Grid c)
lemma affirms (hp:Arc H)(hv:‖s‖<1)(he:‖(a:ℂ)*z‖<1)(hz: ∀ i,Summable (fun j:Key ι=> if peak j=i then (flux H a s z).warp j U else 0)) (i:ι): HasSum (fun j:Key ι=> if peak j=i then (flux H a s z).warp j U else 0) ((H ((a:ℂ)*z) s).warp i U):=by
    let g (j:Key ι):= if peak j=i then (flux H a s z).warp j U else 0
    let p(t:ℂ):=(H t s).warp i U; let f (x:ℕ):= ((a:ℂ)*z)^x • bead x p
    have hA : p 0= (H 0 0).warp i U:= (hp.reading ..).baseS _ hv
    have hC : f 0=p 0:=by simp only [f,bead_baseline,pow_zero,one_smul]
    have hf : HasSum f (p ((a:ℂ)*z)):= ((hp.reading i U).wire s hv).spread he
    have h₀: HasSum (g ∘ Sum.inl) (f 0) :=by rw [hC,hA]; exact selectorOne i (fun j=>(H 0 0).warp j U)
    have h1: f 1=(watt (faint H 1 a s) z).warp i U:=by change ((a:ℂ)*z)^1 • bead 1 p=z • ((a:ℂ)^1 • bead 1 p); rw [smul_smul,pow_one,pow_one,mul_comm]
    let m:=g ∘ Sum.inr
    have h₁: HasSum (m ∘ Sum.inl) (f 1):= by rw [h1]; exact selectorOne i (fun j=> (watt (faint H 1 a s) z).warp j U)
    let Z:= m ∘ Sum.inr
    have hx:∀ (n:ℕ), ∑' j:ι,Z (n,j)=f (n+2):=by
        intro n; rw [tsum_eq_single i]; change ite (i=i) _ _ =_; rw [if_pos rfl]; change z^(n+2) • ((a:ℂ)^(n+2) • bead (n+2) p) = ((a:ℂ)*z)^(n+2) • _; rw [smul_smul,mul_pow,mul_comm (z^_)]
        intro j h; exact if_neg (show j≠ i from h)
    have hZ: Summable Z:=by exact ((hz i).comp_injective Sum.inr_injective).comp_injective Sum.inr_injective
    have h₂ : HasSum Z (p ((a:ℂ)*z)-f 0-f 1):=by
         have hv:= (hasSum_nat_add_iff' 2).mpr hf; have hp:∑' i, Z i= p (_ * z)- ∑ i∈ range 2, f i:=(hZ.tsum_prod).trans ((tsum_congr hx).trans hv.tsum_eq)
         rw [sum_range_succ,sum_range_one] at hp; rw [← sub_add_eq_sub_sub,←hp]; exact hZ.hasSum
    convert (h₀.sum (h₁.sum h₂)) using 1; change p ((a:ℂ)*z)=f 0+(f 1+(p ((a:ℂ)*z)- _- _)); abel
lemma coalesces (hp:Arc H)(hv:‖s‖<1)(he:‖(a:ℂ)*z‖<1) (hz: Summable (fun i=> ‖(flux H a s z).warp i U‖)) : HasSum (tK (H ((a:ℂ)*z) s) t U) (∑' i,tK (flux H a s z) t U i):=by
    refine liftRay peak _ _ U (fun i=> ?_) (affirms H a U hp hv he ?_) (lastK _ _ _ hz)
    · rw [hp.brace]; cases i with| inl i=> rfl| inr i=>cases i<;> rfl
    intro i; refine Summable.of_norm (hz.of_nonneg_of_le (fun _=> norm_nonneg _) fun i=>?_); split; exact le_rfl; exact norm_zero.trans_le (norm_nonneg _)
end Harm
end YM.QCD.Fibre
#print axioms YM.QCD.Fibre.Harm.coalesces
