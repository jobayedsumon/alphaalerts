<?php

namespace App\Console\Commands;

use App\Discord;
use App\Helper;
use App\Models\ChannelNotification;
use Illuminate\Console\Command;
use Illuminate\Support\Facades\Log;

class CheckChannelMessage extends Command
{
    /**
     * The name and signature of the console command.
     *
     * @var string
     */
    protected $signature = 'command:CheckChannelMessage';

    /**
     * The console command description.
     *
     * @var string
     */
    protected $description = 'Check for new messages in discord channels';

    /**
     * Create a new command instance.
     *
     * @return void
     */
    public function __construct()
    {
        parent::__construct();
    }

    /**
     * Execute the console command.
     *
     * @return int
     */
    public function handle()
    {
        $channel_notifications = ChannelNotification::all();
        foreach ($channel_notifications as $channel_notification) {
            try {
                $channel = Discord::channel($channel_notification->channel_id);

                if ($channel && isset($channel->last_message_id) && $channel->last_message_id != $channel_notification->last_message_id) {

                    if ($channel_notification->user->country_code && $channel_notification->user->phone_number && $channel_notification->user->phone_verified_at) {

                        $mobile_no = $channel_notification->user->country_code . $channel_notification->user->phone_number;

                        $lastMessage = Discord::message($channel->id, $channel->last_message_id);
                        $channelLink = Helper::shortUrl('https://discord.com/channels/'.$channel->guild_id.'/'.$channel->id);
                        $project = @$channel_notification->channel->project;
                        $brandText = @$project->white_label_package ? $project->project_name : 'Genus Alpha Tracker';

                        $message = @$lastMessage->content.' | '.$channel->name.' | '.$channel_notification->server_name.' | '.$channelLink.' - '.$brandText;

                        Helper::sendWhatsapp($mobile_no, $message);

                        $channel_notification->last_message_id = $channel->last_message_id;
                        $channel_notification->save();
                    }
                }

            } catch (\Exception $ex) {
                Log::error($ex->getMessage());
            }
        }

    }
}
