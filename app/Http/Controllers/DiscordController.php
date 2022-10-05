<?php

namespace App\Http\Controllers;

use App\Discord;
use App\Models\Channel;
use App\Models\ChannelNotification;
use App\Models\DiscordUser;
use App\Models\Project;
use Illuminate\Http\Request;
use Illuminate\Support\Facades\Auth;
use Illuminate\Support\Facades\DB;
use Laravel\Socialite\Facades\Socialite;
use PHPOpenSourceSaver\JWTAuth\JWTAuth;

class DiscordController extends Controller
{
    public function __construct()
    {
        $this->middleware('auth:api', ['except' => ['discordCallback']]);
        $this->middleware('web', ['only' => ['discordConnect', 'discordCallback']]);
    }

    public function discordConnect(Request $request)
    {
        session()->put('token', $request->get('token'));
        return Socialite::driver ( 'discord' )->setScopes([
            'identify' ,
            'guilds' ,
            'messages.read' ,
        ])->redirect();
    }

    public function discordCallback()
    {
        try {
            $user = Socialite::driver('discord')->user();

            $token = session()->get('token');
            $tokenParts = explode(".", $token);
            $tokenPayload = json_decode(base64_decode($tokenParts[1]));

            $discordUser = DiscordUser::where('discord_id', $user->id)->first();
            if (!isset($discordUser)) {
                $discordUser = new DiscordUser();
            }
            $discordUser->user_id = $tokenPayload->sub;
            $discordUser->discord_id = $user->getId();
            $discordUser->name = $user->getName();
            $discordUser->nickname = $user->getNickname();
            $discordUser->token = $user->token;

            $discordUser->save();

            return redirect()->to('/#/discord');
        } catch (\Exception $e) {
            return redirect()->to('/#/discord');
        }


    }

    public function discordInfo()
    {
        $user = Auth::user();
        $discordUser = DiscordUser::where('user_id', $user->id)->first();

        return response()->json([
            'status' => 'success',
            'discordUser' => $discordUser,
        ]);
    }

    public function discordServers()
    {
        $user = Auth::user();
        $discordUser = DiscordUser::where('user_id', $user->id)->first();
        $token = $discordUser->token;

        $user_servers = Discord::servers($token);

        $projects = Project::all()->pluck ('server_id')->toArray();

        $servers = [];
        foreach ($user_servers as $server) {
            if (in_array($server->id, $projects)) {
                $servers[] = $server;
            }
        }

        return response()->json([
            'status' => 'success',
            'servers' => $servers,
        ]);
    }

    public function discordChannels($id)
    {
        $server_channels = Discord::channels($id);

        $project = Project::where ('server_id', $id)->first();

        $channels = [];
        if ($project && $project->channels) {
            $project_channels = $project->channels()->pluck('channel_id')->toArray();
            foreach ($server_channels as $channel) {
                if (in_array($channel->id, $project_channels)) {
                    $guild = Discord::guildPreview($channel->guild_id);
                    $channel->server_name = $guild->name;
                    $notification = ChannelNotification::where('user_id', \auth()->id())->where('channel_id', $channel->id)->first();
                    $channel->notification = (bool) $notification;
                    $channels[] = $channel;
                }
            }
        }

        return response()->json([
            'status' => 'success',
            'channels' => $channels,
        ]);
    }

    public function discordMessages($id)
    {
        $channel = Channel::where('channel_id', (int) $id)->first();

        $messages = [];
        if ($channel) {
            $messages = Discord::messages ($id);
        }

        return response()->json([
            'status' => 'success',
            'messages' => $messages,
        ]);
    }

    public function guildPreview($id)
    {
        $guild = Discord::guildPreview($id);

        return response()->json([
            'status' => 'success',
            'guild' => $guild,
        ]);
    }

    public function discordDisconnect()
    {
        $user = Auth::user();
        $discordUser = DiscordUser::where('user_id', $user->id)->first();
        if ($discordUser) {
            $discordUser->delete();
        }

        return response()->json([
            'status' => 'success',
        ]);
    }
}
