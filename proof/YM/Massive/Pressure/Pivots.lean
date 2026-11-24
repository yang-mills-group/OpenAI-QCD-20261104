import YM.SectorNext.VACUUM_NORMALIZATION.ForestLine
import YM.SectorNext.VACUUM_NORMALIZATION.Pivots
import YM.SectorNext.VACUUM_NORMALIZATION.Thermal

/-!
# Finish the pivot count in `SectorNext/VACUUM_NORMALIZATION/Pivots`

Keep a FULL tree plus just four independent wraps. Gives 3(v-1) plaques with
full-rank dependencies (property proved here yields integration identity used for
pressure). Selection of wrap plaquettes **uses a tree** in the horizontal slice; it's
therefore possible to leave just those 4 toron variables at the end.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Massive.Pressure.Triangle
open Lattice Tree RG Wilson Finset
open SectorNext.Vacuum SectorNext.Vacuum.Masts
open scoped Matrix.Norms.Frobenius BigOperators Topology Classical
variable {n : Side} {a b s : Axis} {x y : Site n} (hn : 1<n.val)

lemma shortened_zero (h : x b≠0) : ¬wraps (x-step b,b):=by
  unfold wraps; simp only [Pi.sub_apply,step_apply, if_pos]; intro hp; apply h; rw [sub_eq_iff_eq_add.mp hp]; simp

lemma highest_step {q : Axis} (hb : b < q) (h : highest x ≤ b) : (x-step b:Site n) q=0:=by simp [Ne.symm hb.ne,above x (h.trans_lt hb)]
lemma highest_down (hb : b ≤ s) (h : highest x ≤ s) : highest (x-step b) ≤ s:= by apply upto; intro j hj; simp [Ne.symm (hb.trans_lt hj).ne,above x (h.trans_lt hj)]

-- equivalence for counting
lemma trunk_top (x : Site n) (b : Axis) : (x,b)∈(main n hn).trunks ↔ top (x,b) ∧ ¬wraps (x,b):=by
  rw [Forest.trunk_mem_iff]
  constructor
  · rintro ⟨z,hz,he⟩
    rw [reachable] at hz
    change (z-step (highest z), highest z) = (x,b) at he
    rcases Prod.mk.inj he with ⟨rfl,rfl⟩
    exact ⟨(Masts.top_le _).mpr (highest_down le_rfl le_rfl), shortened_zero (highest_on z hz)⟩
  rintro ⟨hp,he⟩
  let z := x+step b
  have hx : z b≠0:=by
    intro hf; apply he; change x b= -1; apply eq_neg_of_add_eq_zero_left; simpa [z] using hf
  have ht : highest z=b:=le_antisymm (upto z b (fun j hj=> by simp [z, Ne.symm hj.ne, show x j = 0 from hp j hj])) (realm _ _ hx)
  refine ⟨z,(reachable z).mpr (fun hf=>hx (congr_fun hf _)),?_⟩
  change (z-step (highest z), highest z) = (_,_); simp [ht,z]

lemma mast_wrap (i : Axis) : wraps (mast n i):=by simp [wraps,mast]
lemma mast_free (i : Axis) : mast n i∉(main n hn).trunks:=fun h => ((trunk_top hn _ _).mp h).2 (mast_wrap i)
lemma mast_inj : Function.Injective (mast n):=fun _ _ h=>congr_arg Prod.snd h

open FlatTree in
lemma main_card : ((main n hn).trunks).card+spare n = Fintype.card (Link n):=by
  have hp := FlatTree.count_clear (main n hn)
  have hh:Fintype.card (main n hn).Free + ((main n hn).trunks).card=Fintype.card (Link n):=by
       rw [show Fintype.card (main n hn).Free=Fintype.card (Link n)- ((main n hn).trunks).card from ?_]; have ht: _ ≤ Fintype.card (Link n):=card_le_univ ((main n hn).trunks); omega
       rw [show Fintype.card (main n hn).Free= _ from Fintype.card_subtype_compl (fun x => x ∈ (main n hn).trunks), Fintype.card_coe]
  rw [Fintype.card_prod,site_card (1:Side)] at hp
  rw [Fintype.card_prod] at hh ⊢; norm_num [spare,Axis] at *; omega
include hn in
lemma count_pivots : Fintype.card (Tor n)=rich n:=by
  let T := (main n hn).trunks; let M := univ.image (mast n)
  have hm : Disjoint T M := disjoint_left.mpr (fun i hi hj=> by obtain ⟨k,_,rfl⟩:= mem_image.mp hj; exact mast_free hn _ hi)
  have hh : M.card=4:=by unfold M; rw [card_image_of_injective _ mast_inj,card_univ,Fintype.card_fin]
  have he : ∀ e, Active e ↔ e ∉ T∪M:=by
    rintro ⟨x,a⟩; simp only [Active, M, T, mem_union, trunk_top, mem_image, mem_univ,true_and,not_or]; apply and_congr_right; intro _; constructor
    · rintro hf ⟨i,hi⟩; have hx : i=a:=congr_arg Prod.snd hi; subst i; exact hf hi.symm
    rintro hf he; exact hf ⟨a,he.symm⟩
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he)]
  rw [Fintype.card_subtype_compl (fun i=> i∈T∪M), Fintype.card_coe,card_union_of_disjoint hm,hh]
  have := spare_four n; have hk := main_card hn; change Fintype.card (Link n)-(T.card+4)=rich n; unfold T; omega

/-- Larger means integrate this link earlier. Define for all links; only need to
compare with other *active* links. -/
def ranking (e : Link n) : ℕ ×ₗ ℕ := if top e
  then toLex (2*e.2.val+1, depth (e.1+step e.2)) else toLex (2*(highest e.1).val, depth e.1)

def Pays (e j : Link n) : Prop := Active e → ranking e < ranking j

def edges (f : Face (Per n)) : Finset (Link n) :=
  let a:= f.2.val.1; let b:=f.2.val.2; {(f.1,a), (f.1+step a,b), (f.1+step b,a), (f.1,b)}

lemma pays_trunk (h : top (x,b)) (hx : ¬wraps (x,b)) (e : Link n) : Pays (x,b) e:=fun he=>(he.1 ⟨h,hx⟩).elim
lemma pays_down (h : top (x,b)) (hz : x b≠0) (e : Link n) : Pays (x-step b,b) e := pays_trunk ((Masts.top_le _).mpr (highest_down le_rfl ((Masts.top_le _).mp h))) (shortened_zero hz) _

-- horizontal pivot: face based below x in direction b.
include hn in
set_option maxHeartbeats 800000 in
lemma horizontal (h : b=highest x) (ha : a<b) : let y:=x-step b
    Pays (y,a) (x,a) ∧ Pays (y,b) (x,a) ∧ Pays (y+step a,b) (x,a):=by
  intro y
  have hu : ¬top (x,a):=fun hi=> ha.not_ge (h.symm ▸ (Masts.top_le _).mp hi)
  have hz : x≠0:=by
    intro ht; rw [ht,highest] at h; simp at h; -- bot
    subst b; exact not_lt_bot ha
  have hp:x b≠0:=h.symm ▸ highest_on x hz
  have hs := (Masts.top_le (x,b)).mpr (show highest x≤b from h.symm.le)
  have hy : highest y≤b:=highest_down le_rfl h.symm.le
  have hd : depth y < depth x:=Nat.lt_of_succ_le (shorten hn x b hp).le
  refine ⟨fun he=>?_, pays_down hs hp _, ?_⟩
  · unfold ranking; rw [if_neg hu]; split
    · rw [Prod.Lex.toLex_lt_toLex]; left; dsimp only []; rw [←h]; have ha : a.val < b.val:=ha; omega
    rw [Prod.Lex.toLex_lt_toLex]; rcases lt_or_eq_of_le hy with hl|hl
    · left; dsimp only []; rw [←h]; have hl: (highest y).val < b.val:=hl; omega
    right; exact ⟨by simp only [←h,hl],hd⟩
  have h' : highest (x+step a)≤b:=upto _ _ (fun j hj=>by simp [Ne.symm (ha.trans hj).ne,above x (h ▸ hj)])
  rw [show y+step a=x+step a-step b from (by unfold y; abel)]; apply pays_down ((Masts.top_le _).mpr h'); simpa [Ne.symm ha.ne]

-- vertical wrap: tree edge in slice y, then crossing in z+step a = x
include hn in
lemma wrap_face (hs : top (x,b)) (hw : wraps (x,b)) (he : Active (x,b)) (h : a=highest (x+step b)) : let z:= x-step a
    a<b ∧ Pays (z,a) (x,b) ∧ Pays (z,b) (x,b) ∧ Pays (z+step b,a) (x,b):=by
  intro z; let y:= x+step b
  have hx : y≠0:=fun h=>he.2 (Prod.ext (eq_neg_of_add_eq_zero_left h) rfl)
  have hx' : a=highest y:=h
  have hk : y b=0:=by change x b=_ at hw; simp [y,hw]
  have hf : y a≠0:=hx'.symm ▸ highest_on y hx
  have ht : highest y ≤ b:=upto _ _ (fun j hj=>by simp [y,Ne.symm hj.ne,show x j=0 from hs j hj]); have ha:a<b:=lt_of_le_of_ne (hx'.le.trans ht) (fun he=>hf (he.symm ▸ hk))
  have hy : z b= -1:= (by simpa [z, ha.ne',wraps] using hw)
  haveI : Fact (1 < n.val) := ⟨hn⟩
  have hy' : z b≠0:=by rw [hy]; simp
  have hl : highest z=b:=le_antisymm (highest_down ha.le ((Masts.top_le _).mp hs)) (realm _ _ hy')
  have hb: top (z,b):=(Masts.top_le _).mpr hl.le
  have hb' : z+step b=y-step a:=by unfold z y; abel
  refine ⟨ha, fun _=>?_,fun he=>?_,?_⟩
  · unfold ranking; rw [if_neg (show ¬ top (z,a) from fun ht=> ha.not_ge (hl ▸ (Masts.top_le _).mp ht)),if_pos hs,Prod.Lex.toLex_lt_toLex]; left; simp [hl]
  · unfold ranking; rw [if_pos hb, if_pos hs, Prod.Lex.toLex_lt_toLex]; right; dsimp only []; exact ⟨rfl,hb'.symm ▸ (Nat.lt_of_succ_le (shorten hn y a hf).le)⟩
  rw [hb']; exact pays_down ((Masts.top_le _).mpr hx'.symm.le) hf _

lemma lens_has (i : Tor n) : i.val∈edges (lens i):=by
  rcases i with ⟨⟨x,b⟩,h⟩; unfold lens; split <;> simp [edges]
lemma no_later (i : Tor n) (hn : 1<n.val) (e : Link n) (he : e∈ edges (lens i)) : e=i.val ∨ Pays e i.val:=by
  rcases i with ⟨⟨x,b⟩,h⟩; unfold lens at he; split at he
  · rename_i hi; let a:=highest (x+step b); change e ∈ {(x-step a,a), (x-step a+step a,b), (x-step a+step b,a),(x-step a,b)} at he; simp only [sub_add_cancel,mem_insert,mem_singleton] at he
    have hw : wraps (x,b):=by by_contra hf; exact h.1 ⟨hi,hf⟩
    obtain ⟨-,h1,h2,h3⟩:=wrap_face hn hi hw h (a:=a) rfl
    rcases he with rfl|rfl|rfl|rfl; exact Or.inr h1; exact Or.inl rfl; exact Or.inr h3; exact Or.inr h2
  · rename_i hi; let a:=highest x
    change e ∈ {(x-step a,b), (x-step a+step b,a), (x-step a+step a,b),(x-step a,a)} at he; simp only [sub_add_cancel,mem_insert,mem_singleton] at he
    obtain ⟨h1,h2,h3⟩:=horizontal hn (b:=a) rfl (lt_of_not_ge (fun ht=> hi ((Masts.top_le _).mpr ht)))
    rcases he with rfl|rfl|rfl|rfl; exact Or.inr h1; exact Or.inr h3; exact Or.inl rfl; exact Or.inr h2
lemma lens_inj (hn : 1 < n.val) : Function.Injective (lens (n:=n)):=by
  intro i j he
  rcases no_later j hn _ (he ▸ lens_has i) with hp|hp
  · exact Subtype.ext hp
  rcases no_later i hn _ (he.symm ▸ lens_has j) with hh | hh; exact Subtype.ext hh.symm; exact ((hh j.property).not_gt (hp i.property)).elim

end YM.Massive.Pressure.Triangle
#print axioms YM.Massive.Pressure.Triangle.lens_inj
