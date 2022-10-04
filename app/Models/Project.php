<?php

namespace App\Models;

use Illuminate\Database\Eloquent\Factories\HasFactory;
use Illuminate\Database\Eloquent\Model;

class Project extends Model
{
    use HasFactory;
    protected $fillable = [
      'project_name',
      'server_id',
    ];

    public function channels()
    {
        return $this->hasMany(Channel::class);
    }
}
