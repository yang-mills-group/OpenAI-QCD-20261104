import YM.Kwick.Figs
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 760000
noncomputable section
namespace YM.Massive.Poised.Plans.Stamp.Stair
open Filter Function Set Lattice Wilson RG Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Poised Poised.Beacon Poised.Display Poised.Stative Poised.Sieve
open Finset Tawny Tawny.Cast Tawny.Cast.Rays Tawny.Cast.Carnal Tawny.Cast.TableT Tawny.Pane Tawny.BendR
open Oriole Counting Counting.Click PCAC Patria.Gall.Seals Patria.Gall
local notation "Z"=> RawVec 10
variable (x y:Z)(p q:Multi 10)(a b:Flavor 6)(j t:Fiber)
local notation "B"=> bee
local notation "L₀"=> (0:Multi 10)
local notation "Ξ"=> leadR
local notation "r"=> bet 0
-- simpl via explicit table expansion.
lemma lowly(x:Values 7)(q:Fin 3→ℂ): bet 0 (plaza (x,q))=∑ i:Flavor 6, (x i 0 • bee i+x i 1 • beeA i):=by
      rw [bet,vaultE, if_neg (show tierQ 3≠tierQ 0 from (by decide)),zero_smul]; let p(i:Flavor 6)(j):=(if tierQ (τ7 j)=tierQ 0 then (1:ℂ) else 0)*x i j
      change vectorY p+ ocean 0=_; rw[show ocean 0=0 from (by simp[ocean]), add_zero]; unfold vectorY; apply sum_congr rfl; intro i _; unfold vectorZ p; have he(j k:Fin 4):tierQ j=tierQ k ↔ j=k:=by decide +revert
      simp only[he]; rw[if_pos (show τ7 0=0 from rfl),if_pos (show τ7 1=0 from rfl),if_neg (show τ7 2 ≠0 from (by decide)),if_neg (show τ7 3 ≠ 0 from (by decide)),if_neg (show τ7 4 ≠ 0 from (by decide)),if_neg (show τ7 5≠0 from (by decide)),if_neg (show τ7 6≠0 from (by decide))]; simp only [one_mul,zero_mul,zero_smul,add_zero]

local notation "Ql" z:arg=> seekC a j t z
private lemma tilt_quiet (x:Z)(J:Labels.Jet su)(h:vaultP (tierQ 0) x=x): tiltX a j t J (x.val (0:Axis))=0:=by
    nth_rw 1[←h]; let y:= (x.val (0:Axis)).val; change Tawny.skin J (geometry 10 ((kind 10 (tierQ 0)) y)) ((L₀,j),a) ((L₀,t),a)=0; have hp : geometry 10 ((kind 10 (tierQ 0)) y) =0:=by
         apply (zBasis 10).repr.injective; ext i; change coord i (geometry _ _)=coord i 0; rw [geo_basis,kind_S,map_zero]; by_cases he:crest i=tierQ 0; rw [if_neg (show UV.weight i≠10 from fun h=>by have he:UV.weight i=8:= congr_arg Prod.fst he; omega)]; rw[if_neg he,ite_self]
    rw [hp,map_zero]; rfl
-- direct bill. high q for prism height.C
private lemma billS (p q:Multi 10)(U:Flavor 6)(hp:spinWeight p+spinWeight q=10) : chipK p q a ((bee U).val (0:Axis))=0∧chipK p q a ((beeA U).val (0:Axis))=0:=by
     rw[coinedP,coinedP]; have hh(i:Axis): (p≠L₀∨q≠ Ξ i)∧ (q ≠L₀ ∨ p ≠ Ξ i):=by constructor <;> by_contra! h <;> rw[h.1,h.2,gradeV,gradeL] at hp <;> omega
     let x:= (0:Axis); have h1:qv a p q (bee U)=0:=by change prism0 a p q ((bee U).val x).val=0; rw[bee_val,beta_up,map_add,bareB,bareB]; have ht:= hh x; rw[if_neg (by tauto),if_neg (by tauto),zero_add]
     have h2:qv a p q (beeA U)=0:=by
           change prism0 a p q ((beeA U).val x).val=0; rw [sea_val,AddSubmonoidClass.coe_finsetSum,map_sum]; apply sum_eq_zero; intro i _; rw [sea_up,map_add,bareB,bareB]; have ht:= hh i; rw [if_neg (by tauto),if_neg (by tauto),zero_add]
     rw [h1,h2,wave_zero]; exact ⟨rfl,rfl⟩
lemma lets : lookQ (bet 0 x)=0:=by
      obtain ⟨⟨u,v⟩,rfl⟩:= certified.2 x; rw [lowly]; rw [map_sum]; refine sum_eq_zero fun i _=> ?_
      have hx (A:Z)(hp:vaultP (tierQ 0) A=A)(h:∀ (p q:Multi 10)(a:Flavor 6), spinWeight p + spinWeight q=10→ chipK p q a (A.val (0:Axis))=0): lookQ A=0:=by
           funext a j; rcases j with ⟨j,t⟩; change awake2 _ _ _ _ _ _ (A.val (0:Axis))=0; rw [awake2,LinearMap.add_apply,tilt_quiet _ _ _ _ _ hp,add_zero]; unfold fringe; simp only [LinearMap.coe_mk,AddHom.coe_mk]; let x:=(0:Axis); let y:=(1:Axis); rw [h (ηR 0 1) L₀ a (by rw[gradeV,gradeH]), h L₀ (ηR 0 1) a (by rw[gradeV,gradeH]),h (Ξ 0) (Ξ 1) _ (by rw[gradeL,gradeL])]; simp
      have ht(k:Fin 7)(h:τ7 k=0):vaultP (tierQ 0) (slots7 i k)=slots7 i k:= Subtype.ext (funext fun a=> (blastT (tierQ 0) i k a).trans (by rw[h,if_pos rfl,one_smul]))
      rw [map_add,map_smul,map_smul,hx (bee i) (ht 0 rfl) (fun p q a he=>(billS a p q i he).1),hx (beeA i) (ht 1 rfl) (fun p q a he=>(billS a p q i he).2),smul_zero,smul_zero,add_zero]
open Perla
lemma lastQ : lookQ (bet 3 x)=0:=by
     obtain ⟨⟨u,v⟩,rfl⟩:= certified.2 x; have hp(i:Fin 7):tierQ (τ7 i) ≠ tierQ 3:=by decide +revert
     rw [bet,vaultE]; simp_rw[if_neg (hp _),zero_mul]; change lookQ (plaza ((0:Values 7),_))=0; let t : Fin 3→ℂ:=v; rw[tabsT]; simp only [Pi.zero_apply,zero_smul,sum_const_zero,zero_add]; rw [map_sum]; refine sum_eq_zero fun i _=>?_ ; rw [map_smul]; suffices hs: lookQ (harps i)=0 by rw[hs,smul_zero]
     funext p j; rcases j with ⟨j,k⟩; change awake2 _ _ _ _ _ _ ((harps i).val (0:Axis))=0
     let V:=awake2 0 1 p j k Gpick; have h(a b i j k:Axis):V (GE a b i j k)=0:= plainU p _ _ _ _ _ _ (StressFlux.pairDeriv su a b i j k).val rfl
     have he : i=0 ∨ i=1∨i=2:=by omega
     rcases he with ht|ht|ht
     · rw [ht,show harps 0=_ from (show harps 0=leapV from rfl),oleap,map_sum]; exact sum_eq_zero fun i _=>h ..
     · rw [ht,show harps 1=lunar from rfl, olun,map_sum]; simp_rw [map_sum]; exact sum_eq_zero fun j _=> sum_eq_zero fun i _=>h ..
     rw [ht,show harps 2=eulerV from rfl,oeul,map_sum]; simp_rw [map_sum]; exact sum_eq_zero fun i _=>sum_eq_zero fun k _=>h ..
lemma lineU : lookQ x=lookQ (bet 1 x)+lookQ (bet 2 x):=by
     nth_rw 1[bill_zero x]; rw [map_sum,Fin.sum_univ_four, lets,lastQ,add_zero,zero_add]
lemma predV(T v:ℝ)(X:Z) : (↑(bud 2 T v):ℂ) • lookQ X=(T:ℂ) • lookQ (Stair.stack 1 T v X) + lookQ (Stair.stack 2 T v X):=by nth_rw 1[lineU]; unfold stack; rw[smul_add,map_smul,map_smul,smul_smul]; congr 2; unfold bud; change (↑(T^1*v^2):ℂ)= _ * (↑(T^0*v^2):ℂ); norm_num
end YM.Massive.Poised.Plans.Stamp.Stair
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.predV
