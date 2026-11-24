import YM.QCD.Grove.Mike
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grove
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f:Side}{N n:ℕ}
open Animals
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Slide Trio.Sharp
-- layout
variable {C:Side}{D D' w j:ℕ}{d r t t' p p':ℝ}{B:BudgetPoint}
open AnalyticBridge VerifiedReset -- conflicts.
section beacon
variable {m s s' q:ℕ}{L:Side}{Y: Stars→Side} (R:∀ i:Stars,(Y i).val=2*(m*Slide.roller i.val)) (F:Stars→Type) (S:∀ i:Stars,Finset (F i))(Z:∀ i, Gem (Y i) N (F i)) (T:Finset I)(P:Gem c N I)
-- Omits χ.. Charged
noncomputable def palaceB (s:ℕ): Gem c N (Site c):=⟨fun i=> Grove.wharf c s i, fun i=> Reggae.ocean c N ∘ elder R F S Z i⟩
noncomputable def locY (s q:ℕ)(B: BudgetPoint): Ruby.Hue c N (Site c):=⟨fun i=> neighbors q i,fun i=> Reggae.ocean c N ∘ relic R F S Z T P i B s⟩
set_option quotPrecheck false
local notation "P₀"=>palaceB R F S Z (c:=c) s
local notation "L₀"=>locY R F S Z T P s q B
lemma soda (x:Site c)(U:Grid c): letters P₀ B.threshold U x= Reggae.ocean c N (masked B.threshold (neighbors s x) (elder R F S Z x) U):=by
    unfold letters; by_cases he: Healthy B.threshold (neighbors s x) U; · rw [masked_eq _ _ _ _ he]; exact masked_eq _ _ _ _ he
    rw [masked_ne _ _ _ _ he,map_zero]; exact masked_ne _ _ _ _ he
lemma minted (hp:81*m ≤ s)(hv:∀ i,SoilB (S i) (Z i) B w t')(ht:0≤t'): Dyed (P₀):=by
    refine ⟨fun j U k=>?_,fun i V W _=> Reggae.thorough ..,fun i V=> Reggae.thorough ..⟩; have h:elder R F S Z j (gauge k U)=elder R F S Z j U:=(stalks R F S Z hv hp ht j).symmetry k U
    suffices he:sways (Lat.rotates N k) (Reggae.ocean c N (elder R F S Z j (gauge k U)))= _ from congr_arg Subtype.val (show sways _ _=(P₀).view j U from he)
    rw [h]; exact Reggae.thorough ..
noncomputable def aroma (c:Side)(G:Site c→ Grid c→ℝ):ℝ:=(Fintype.card (Site c):ℝ)*G 0 1
noncomputable def stored {B:BudgetPoint} (U:Grid c):ℝ := ∑ i:Site c,crests (cloudQ T P (B:=B)) i U -- explicit param
local notation "H₀"=>aroma c (crests (duskQ T P))
lemma argent (U:Grid c): Reggae.ocean c N (stored (B:=B) T P U)= Reggae.ocean c N H₀+ (∑ x:Site c,letters P₀ B.threshold U x) +∑ i:Site c,(L₀).mean i U:=by
   unfold Grove.stored; rw [note_eq R F S Z T P (s:=s) (B:=B), map_add,map_add,map_sum,map_sum]; simp_rw [soda]; rfl
-- Vec cash ψ. no scalar sign hidden
variable (h:SoilB T P B w t)
include h
lemma psiSum (U:Grid c):
    let M:= ∑ i∈T, letters P B.threshold U i; M=Reggae.ocean c N (Reggae.river _ _ M)+ (∑ i:Site c,letters (helm P T s') B.threshold U i) +∑ i:Site c,(aleph P T B s').mean i U:=by
       intro M; have hv i (hi:i∈ T) := wonders (P.view i) (P.addr i).support B.threshold (h.gauge i hi) (h.fit i hi) (h.real i hi) (h.fees i hi|>.choose_spec.gated); have hp: Regal c N M=M:=by unfold M; rw [map_sum]; exact sum_congr rfl fun i hi=> ((hv i hi).2 U).2.1
       have hz: Port.sparkF c N (mud M)= Reggae.ocean c N (Reggae.river _ _ M):=by
         rw [realP hp]; apply Subtype.ext; simp only [Port.sparkF]; change (-(Reggae.river c N M:ℝ):ℂ) • (1:Grass.Alg _) = _; change _ • _=-(((↑(Reggae.river c N M):ℂ)) • (1:Grass.Alg _)); rw [neg_smul] -- coercions
       have hh (x:Site c): letters (helm P T s') B.threshold U x+ (aleph P T B s').mean x U= buds x N M:=by
           let Z:= cashD T P (B:=B) U x; let X:= letters (helm P T s') B.threshold U x; rw [show _+ (aleph P T B s').mean x U = buds x N Z from (add_sub_cancel ..)]; unfold Z cashD M; rw [map_sum,map_sum]; refine sum_subset (filter_subset ..) fun i hi hp=>sprout x (P.addr i).support _ ((hv i hi).2 U|>.2.2) (fun he=>hp (mem_filter.mpr ⟨hi,he⟩))
       rw [add_assoc,← sum_add_distrib]; simp_rw [hh]; exact (sourcesR M).trans (congr_arg₂ _ hz rfl)
omit h
-- Linear property. orientation homs issue use spice.passL /L.
noncomputable def potion (f: Grid c→ EvenA c N) (U:Grid c):EvenA c N:=averageC c •∑ i:Strut c, Patron.spice i (f (Strut.sky i U))
lemma crestedX (f g:Grid c→EvenA c N)(U: Grid c): potion (f+g) U=potion f U+potion g U:=by unfold potion; simp only [Pi.add_apply,map_add,sum_add_distrib,smul_add]
lemma vaultX (Q: Gem c N I) (t:ℝ) [Fintype I] (U:Grid c): potion (fun V=> ∑ i, letters Q t V i) U= Patron.total (glean Q) t U:=by unfold Patron.total; rw [tsum_fintype]; simp_rw [Fintype.sum_prod_type, shapeS]; unfold potion; simp_rw [smul_sum,map_sum,smul_sum]; rw [Fintype.sum_prod_type]
lemma leaseX (Q:Ruby.Hue c N I)[Fintype I](V:Grid c): potion (fun W=>∑ i,Q.mean i W) V=∑' i,(Ruby.HGrace Q).mean i V:=by rw [tsum_fintype,Fintype.sum_prod_type]; unfold potion; simp_rw [map_sum,smul_sum]; rfl
lemma oceanic (V:Grid c): potion (fun V=> Reggae.ocean c N (Reggae.river _ _ (∑ i∈T,letters P B.threshold V i))) V=Reggae.ocean c N (stored (B:=B) T P V):=by
   unfold Grove.stored crests potion; rw [← Finset.mul_sum,Finset.sum_comm]; change _=Reggae.ocean c N (averageC c • _); rw [map_smul, map_sum]; congr 1; apply sum_congr rfl; intro i _; rw [show Patron.spice i (Reggae.ocean _ _ _) = _ from Reggae.thorough ..]; apply congr_arg; rw [show (∑ x:Site c, viewS (cloudQ (B:=B) T P) i x V)=_ from Equiv.sum_comp (Strut.act i).symm (fun x=>cloudQ T P (B:=B) x (Strut.sky i V))]; symm; exact populous _ (fun i V=>letters P _ V i) T _
lemma hearty (V:Grid c) (s:Strut c) : stored (B:=B) T P (Strut.sky s V)=stored (B:=B) T P V:=by unfold Grove.stored; simp_rw [lunarS]; exact Equiv.sum_comp (Strut.act s) (fun i=> crests (cloudQ T P (B:=B)) i V)
lemma devour (f:Grid c→ℝ)(V:Grid c) (hf: ∀ i:Strut c,f (Strut.sky i V)=f V): potion (Reggae.ocean c N ∘ f) V= Reggae.ocean c N (f V):=by
   unfold potion; simp_rw [Function.comp_apply,hf, show ∀ s:Strut c,Patron.spice s (Reggae.ocean c N (f V))=Reggae.ocean _ _ _ from fun s=> Reggae.thorough ..,sum_const, ← Nat.cast_smul_eq_nsmul ℝ,card_univ, smul_smul,averageC,inv_mul_cancel₀ (show (Fintype.card (Strut c):ℝ)≠0 from (by positivity)),one_smul]
include h
lemma medulla (V:Grid c): potion (fun U=> ∑ i∈T,letters P B.threshold U i) V= Reggae.ocean c N (H₀) + (Patron.total (glean (helm P T s')) B.threshold V + Patron.total (glean (P₀)) B.threshold V) + ((∑' i,(Ruby.HGrace (aleph P T B s')).mean i V) +(∑' i,(Ruby.HGrace (L₀)).mean i V)):=by
    let f := fun U=> ∑ i∈T,letters P B.threshold U i; let a U:= Reggae.ocean c N (Reggae.river _ _ (f U)); let b U:= ∑ i, letters (helm P T s') B.threshold U i; let c' U:= ∑ i,(aleph P T B s').mean i U
    have hz :f=a+b+c':=funext fun i=>psiSum T P h i -- order
    have hx:potion a V=potion (Reggae.ocean c N ∘ stored (B:=B) T P) V:=Eq.trans (oceanic ..) (devour _ _ (hearty T P V)).symm
    let k (_:Grid c):= Reggae.ocean c N (H₀); let u U:=∑ x:Site c,letters P₀ B.threshold U x; let z U:= ∑ i:Site c,(L₀).mean i U
    have he: Reggae.ocean c N ∘ stored (B:=B) T P=k+u+z:=funext fun i=>argent R F S Z T P i
    rw [show _=potion f V from rfl,hz,crestedX,crestedX,hx,he,crestedX,crestedX,show potion k V=k V from devour (fun _=> H₀) V (fun _=> rfl),show potion b _=_ from vaultX ..,show potion u _=_ from vaultX ..,show potion z _=_ from leaseX ..,show potion c' _=_ from leaseX ..]; unfold k; abel
end beacon
end YM.QCD.Grove
#print axioms YM.QCD.Grove.medulla
