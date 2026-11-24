import YM.QCD.Grove.Fair
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
variable (A:C.val=c.val*D)(M:C.val=f.val*D')(P:Gem c N I)(Q:Gem C N J)(S:Gem f N V)(T:Finset I)(T':Finset J)(T₀:Finset V)(g v:Site C→ℂ){b ε:ℝ}
set_option quotPrecheck false
local notation "Δ"=> normal (Deck.divides A) A
local notation "Δ'"=> normal (Deck.divides M) M
variable (ha: LiftQ (normal (Deck.divides A) A) P Q T T' g B w)(hv: LiftQ (normal (Deck.divides M) M) S Q T₀ T' v B w) (ht:SoilB T' Q B w t') (hu:SoilB T₀ S B w t') (hw:SoilB T P B w t')
include ha
lemma auraS (r:Strut C)(x:Site C)(U:Grid c)(hU:flags B.threshold U=∅): viewS (duskQ T P) (r.1, Macrame.splitter (Deck.divides A) r.2) ((Δ).cut x) U=viewS (duskQ T' Q) r x ((Δ).links U):=by
   let s :Strut c:= (r.1, (Δ).cut r.2); have he:= Folding.pegs Δ (Deck.divides A) rfl (v:=r) (u:=s) rfl rfl
   have hp: Strut.sky r ((Δ).links U)= (Δ).links (Strut.sky s U):=by
       funext i; obtain ⟨x,j⟩:=i; change (posDir j|>.rotate r.1).read ((Δ).links U) (Strut.act r x)= (posDir j|>.rotate s.1).read U (Strut.act s ((Δ).cut x)); rw [← show (Δ).cut (Strut.act r x)=Strut.act s ((Δ).cut x) from (congr_fun he.2 x)]; exact (Δ).read .. -- check lemma
   change viewS (duskQ T P) s _ _=_; unfold viewS; rw [hp, show (Strut.act s).symm ((Δ).cut x)=(Δ).cut ((Strut.act r).symm x) from ?_]; · exact (ha.rays _ _ (Pane.tranquility (t:=B.threshold) U hU _ _)).2
   apply (Strut.act s).injective; rw [Equiv.apply_symm_apply, ← show (Δ).cut (Strut.act r ((Strut.act r).symm x))=Strut.act s ((Δ).cut ((Strut.act r).symm x)) from congr_fun he.2 _,Equiv.apply_symm_apply]
lemma dust_jump (x: Site C)(U : Grid c)(hx:flags B.threshold U=∅) : crests (duskQ T P) ((Δ).cut x) U=crests (duskQ T' Q) x ((Δ).links U):=by
   let f(r: Strut c):= viewS (duskQ T P) r ((Δ).cut x) U; let q (r:Strut C):=viewS (duskQ T' Q) r x ((Δ).links U); let p (r:Strut C):Strut c:=(r.1,(Δ).cut r.2); have hP (i):q i=f (p i):=Eq.symm (auraS A P Q T T' g ha i x U hx) -- need args
   have hh :(∑ i:Strut C,q i)= (D^4:ℕ) • ∑ i:Strut c,f i:=by
      simp_rw [hP,Fintype.sum_prod_type,smul_sum]; refine sum_congr rfl fun i _=> by rw [← Finset.smul_sum]; exact (Shingle.multiplied _ (Δ).fold (fun j=>f (i,j))) -- signatures
   have hD:Fintype.card (Strut C) = D^4 * Fintype.card (Strut c):=by unfold Strut; rw [Fintype.card_prod,Fintype.card_prod, Shingle.received _ (Δ).fold]; ring
   have ht: 0 < D:=Nat.pos_of_ne_zero (fun he=>by have h:=C.pos; rw [A,he,Nat.mul_zero] at h; omega)
   unfold crests; change _ * (∑ i,f i)= (Fintype.card (Strut C):ℝ)⁻¹*(∑ i,q i); rw [hh,hD,nsmul_eq_mul]; push_cast; field_simp
include hv ht
lemma tendingU (hm:0≤t')(hk:2*(w+1)< C.val): Trio.Compatible (crests (duskQ T P)) (crests (duskQ T₀ S)) B w:=by
    intro x y U V hU hV hx
    have he (f :Side) (T: Site f→ Grid f→ℝ)(p: Site f)(U:Grid f):crests T p U=crests T 0 (translate p U):=by
       have hp := lunarS T (1,p) 0 U; rw [show Strut.sky (1,p) U= translate p U from pull_one ..,show Strut.act (1,p) 0=p from ?_] at hp; exact hp.symm
       change (Lattice.affine 1 p 0)=_; simp [Lattice.affine]
    rw [he .., he f _ y V,show (0:Site c)=(Δ).cut 0 from (map_zero (splitter (Deck.divides A))).symm, dust_jump A P Q T T' g ha 0 _ (by rw [← pull_one]; exact Pane.tranquility _ hU _ _),show (0:Site f)=(Δ').cut 0 from (map_zero (splitter (Deck.divides M))).symm]; -- exact others
    have hp := dust_jump M S Q T₀ T' v (by assumption) 0 (translate y V) (by rw [← pull_one]; exact Pane.tranquility _ hV _ _)
    rw [hp]; apply (poetry ht hm 0).sites; apply Slide.readNear _ hk; rw [Slide.rolls, Slide.rolls,map_zero,map_zero,Slide.increases,Slide.increases]; exact hx
end YM.QCD.Grove
